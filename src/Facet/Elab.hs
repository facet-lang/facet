{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | This module defines the /elaboration/ of terms in 'S.Expr' into values in 'Type'.
--
-- Elaboration is the only way 'Type's are constructed from untrusted terms, and so typechecking is performed at this point. If elaboration succeeds and a 'Type' is returned, that 'Type' does not require further verification; hence, 'Type's elide source span information.
module Facet.Elab
( -- * General
  unify
, switch
, as
, lookupInContext
, lookupInSig
, resolveQ
, resolveC
, meta
, instantiate
, hole
, app
, (|-)
  -- * Errors
, setSpan
, Err(..)
, ErrReason(..)
, couldNotSynthesize
, freeVariable
, expectMatch
, expectFunction
  -- * Warnings
, Warn(..)
, WarnReason(..)
, warn
  -- * Unification
, ElabContext(..)
, sig_
  -- * Machinery
, Elab(..)
, depth
, elabWith
, elab
, elabType
, elabTerm
, elabSynth
, check
, Check(..)
, mapCheck
, Synth(..)
, mapSynth
, bind
, Bind(..)
, mapBind
) where

import Control.Algebra
import Control.Applicative (Alternative)
import Control.Carrier.Error.Church
import Control.Carrier.Fresh.Church
import Control.Carrier.Reader
import Control.Carrier.State.Church
import Control.Effect.Empty
import Control.Effect.Lens (view)
import Control.Lens (Lens', lens)
import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.Foldable (asum)
import Data.Semialign.Exts
import Facet.Carrier.Trace.Output as Trace
import Facet.Context as Context
import Facet.Core.Module
import Facet.Core.Term as E
import Facet.Core.Type as T
import Facet.Effect.Write
import Facet.Graph as Graph
import Facet.Lens
import Facet.Name hiding (L, R)
import Facet.Span (Span(..))
import Facet.Stack
import Facet.Syntax
import GHC.Stack
import Prelude hiding (span, zipWith)

-- TODO:
-- - clause/pattern matrices
-- - tacit (eta-reduced) definitions w/ effects
-- - mutual recursion? does this work already? who knows
-- - datatypes containing computations

-- General

-- FIXME: should we give metas names so we can report holes or pattern variables cleanly?
meta :: Has (State Context :+: State Subst) sig m => Maybe Type ::: Type -> m Meta
meta (v ::: _T) = do
  m <- state (declareMeta _T)
  m <$ modify (|> Flex m v _T)


-- FIXME: does instantiation need to be guided by the expected type?
instantiate :: Algebra sig m => (a -> TExpr -> a) -> a ::: Type -> Elab m (a ::: Type)
instantiate inst = go
  where
  go (e ::: _T) = case _T of
    VTForAll _ _T _B -> do
      m <- meta (Nothing ::: _T)
      go (inst e (TVar (TMetavar m)) ::: _B (metavar m))
    _                -> pure $ e ::: _T


switch :: (HasCallStack, Has (Throw Err :+: Trace) sig m) => Synth m a -> Check m a
switch (Synth m) = Check $ trace "switch" . \ _K -> m >>= \ (a ::: _K') -> a <$ unify _K' _K

as :: Has Trace sig m => Check m Expr ::: Check m TExpr -> Synth m Expr
as (m ::: _T) = Synth $ trace "as" $ do
  eval <- gets evalIn
  _T' <- eval <$> check (_T ::: VKType)
  a <- check (m ::: _T')
  pure $ a ::: _T'

resolveWith
  :: Has (Throw Err :+: Trace) sig m
  => (forall m . Alternative m => Name -> Module -> m (Q Name :=: Maybe Def ::: Type))
  -> Q Name
  -> Elab m (Q Name :=: Maybe Def ::: Type)
resolveWith lookup n = asks (\ ElabContext{ module', graph } -> lookupWith lookup n module' graph) >>= \case
  []  -> freeVariable n
  [v] -> pure v
  ds  -> ambiguousName n (map (\ (q :=: _ ::: _) -> q) ds)

resolveC :: Has (Throw Err :+: Trace) sig m => Q Name -> Elab m (Q Name :=: Maybe Def ::: Type)
resolveC = resolveWith lookupC

resolveQ :: Has (Throw Err :+: Trace) sig m => Q Name -> Elab m (Q Name :=: Maybe Def ::: Type)
resolveQ = resolveWith lookupD

lookupInContext :: Q Name -> Context -> Maybe (Index, Type)
lookupInContext (m:.:n)
  | m == Nil  = lookupIndex n
  | otherwise = const Nothing

-- FIXME: probably we should instead look up the effect op globally, then check for membership in the sig
lookupInSig :: Q Name -> Module -> Graph -> [Type] -> Maybe (Q Name ::: Type)
lookupInSig (m :.: n) mod graph = fmap asum . fmap $ \case
  VTNe (TGlobal q@(m':.:_) :$ _) -> do
    guard (m == Nil || m == m')
    _ :=: Just (DInterface defs) ::: _ <- lookupQ q mod graph
    _ :=: _ ::: _T <- lookupScope n defs
    pure $ m':.:n ::: _T
  _                            -> Nothing


hole :: Has (Throw Err :+: Trace) sig m => Name -> Check m a
hole n = Check $ \ _T -> err $ Hole n _T

app :: Has (Throw Err :+: Trace) sig m => (a -> b -> c) -> Synth m a -> Check m b -> Synth m c
app mk f a = Synth $ trace "app" $ do
  f' ::: _F <- synth f
  (_ ::: _A, _B) <- expectFunction "in application" _F
  a' <- check (a ::: _A)
  pure $ mk f' a' ::: _B


(|-) :: (HasCallStack, Has Trace sig m) => Name ::: Type -> Elab m a -> Elab m a
-- FIXME: this isn’t _quite_ the shape we want to push onto the context because e.g. constructor patterns can bind multiple variables but they’d all have the same icit & signature.
-- FIXME: should this do something about the signature?
n ::: _T |- b = trace "|-" $ do
  i <- depth
  -- FIXME: should the context allow names in Maybe?
  modify (|> Rigid n _T)
  a <- b
  let extract (gamma :> Rigid{}) | i == level (Context gamma) = gamma
      extract (gamma :> e@Flex{})                             = extract gamma :> e
      extract (_     :> _)                                    = error "bad context entry"
      extract Nil                                             = error "bad context"
  a <$ modify (Context . extract . elems)

infix 1 |-


depth :: Has (State Context) sig m => m Level
depth = gets level


-- Errors

setSpan :: Has (Reader ElabContext) sig m => Span -> m a -> m a
setSpan = locally span_ . const


data Err = Err
  { span      :: Span
  , reason    :: ErrReason
  , context   :: Context
  , callStack :: Stack Message -- FIXME: keep source references for each message.
  }

data ErrReason
  = FreeVariable (Q Name)
  -- FIXME: add source references for the imports, definition sites, and any re-exports.
  | AmbiguousName (Q Name) [Q Name]
  | CouldNotSynthesize String
  | Mismatch String (Either String Type) Type
  | Hole Name Type
  | Invariant String


-- FIXME: apply the substitution before showing this to the user
err :: Has (Throw Err :+: Trace) sig m => ErrReason -> Elab m a
err reason = do
  ctx <- get
  span <- view span_
  callStack <- Trace.callStack
  throwError $ Err span reason ctx callStack

mismatch :: Has (Throw Err :+: Trace) sig m => String -> Either String Type -> Type -> Elab m a
mismatch msg exp act = err $ Mismatch msg exp act

couldNotUnify :: Has (Throw Err :+: Trace) sig m => String -> Type -> Type -> Elab m a
couldNotUnify msg t1 t2 = mismatch msg (Right t2) t1

couldNotSynthesize :: Has (Throw Err :+: Trace) sig m => String -> Elab m a
couldNotSynthesize = err . CouldNotSynthesize

freeVariable :: Has (Throw Err :+: Trace) sig m => Q Name -> Elab m a
freeVariable n = err $ FreeVariable n

ambiguousName :: Has (Throw Err :+: Trace) sig m => Q Name -> [Q Name] -> Elab m a
ambiguousName n qs = err $ AmbiguousName n qs


-- Warnings

data Warn = Warn
  { span   :: Span
  , reason :: WarnReason
  }

data WarnReason
  = RedundantCatchAll Name


warn :: Has (Write Warn) sig m => WarnReason -> Elab m ()
warn reason = do
  span <- view span_
  write $ Warn span reason


-- Patterns

expectMatch :: Has (Throw Err :+: Trace) sig m => (Type -> Maybe out) -> String -> String -> Type -> Elab m out
expectMatch pat exp s _T = maybe (mismatch s (Left exp) _T) pure (pat _T)

expectFunction :: Has (Throw Err :+: Trace) sig m => String -> Type -> Elab m (Either Name [Type] ::: Type, Type)
expectFunction = expectMatch (\case{ VTArrow n t b -> pure (n ::: t, b) ; _ -> Nothing }) "_ -> _"


-- Unification

data ElabContext = ElabContext
  { graph   :: Graph
  , mname   :: MName
  , sig     :: [Type]
  , module' :: Module
  , span    :: Span
  }

sig_ :: Lens' ElabContext [Type]
sig_ = lens sig (\ e sig -> e{ sig })

span_ :: Lens' ElabContext Span
span_ = lens (span :: ElabContext -> Span) (\ e span -> (e :: ElabContext){ span })


onTop :: (HasCallStack, Has (Throw Err :+: Trace) sig m) => (Level -> Meta :=: Maybe Type ::: Type -> Elab m (Maybe Suffix)) -> Elab m ()
onTop f = trace "onTop" $ do
  ctx <- get
  (gamma, elem) <- case elems ctx of
    gamma :> elem -> pure (Context gamma, elem)
    Nil           -> err $ Invariant "onTop in empty context"
  put gamma
  case elem of
    Flex n v _T -> f (level gamma) (n :=: v ::: _T) >>= \case
      Just v  -> modify (<>< v)
      Nothing -> modify (|> elem)
    _         -> onTop f <* modify (|> elem)

-- FIXME: we don’t get good source references during unification
unify :: forall m sig . (HasCallStack, Has (Throw Err :+: Trace) sig m) => Type -> Type -> Elab m ()
unify t1 t2 = trace "unify" $ type' t1 t2
  where
  nope = couldNotUnify "mismatch" t1 t2

  type' t1 t2 = trace "unify type'" $ case (t1, t2) of
    (VTNe (TMetavar v1 :$ Nil), VTNe (TMetavar v2 :$ Nil)) -> trace "flex-flex" $ onTop $ \ _ (g :=: d ::: _K) -> case (g == v1, g == v2, d) of
      (True,  True,  _)       -> restore
      (True,  False, Nothing) -> replace [v1 :=: Just (metavar v2) ::: _K]
      (False, True,  Nothing) -> replace [v2 :=: Just (metavar v1) ::: _K]
      (True,  False, Just t)  -> type' t (metavar v2) >> restore
      (False, True,  Just t)  -> type' (metavar v1) t >> restore
      (False, False, _)       -> type' (metavar v1) (metavar v2) >> restore
    (VTNe (TMetavar v1 :$ Nil), t2)                        -> solve v1 t2
    (t1, VTNe (TMetavar v2 :$ Nil))                        -> solve v2 t1
    (VKType, VKType)                                       -> pure ()
    (VKType, _)                                            -> nope
    (VKInterface, VKInterface)                             -> pure ()
    (VKInterface, _)                                       -> nope
    (VTForAll n t1 b1, VTForAll _ t2 b2)                   -> do { type' t1 t2 ; d <- depth ; n ::: t1 |- type' (b1 (T.free d)) (b2 (T.free d)) }
    (VTForAll{}, _)                                        -> nope
    (VTArrow _ a1 b1, VTArrow _ a2 b2)                     -> type' a1 a2 >> type' b1 b2
    (VTArrow{}, _)                                         -> nope
    (VTComp s1 t1, VTComp s2 t2)                           -> sig s1 s2 >> type' t1 t2
    (VTComp{}, _)                                          -> nope
    (VTNe (v1 :$ sp1), VTNe (v2 :$ sp2))                   -> var v1 v2 >> spine telim sp1 sp2
    (VTNe{}, _)                                            -> nope
    (VTString, VTString)                                   -> pure ()
    (VTString, _)                                          -> nope

  var v1 v2 = trace "unify var" $ case (v1, v2) of
    (TGlobal q1, TGlobal q2)   -> unless (q1 == q2) nope
    (TGlobal{}, _)             -> nope
    (TFree v1, TFree v2)       -> unless (v1 == v2) nope
    (TFree{}, _)               -> nope
    (TMetavar m1, TMetavar m2) -> unless (m1 == m2) nope
    (TMetavar{}, _)            -> nope

  telim t1 t2 = case (t1, t2) of
    (TEInst t1, TEInst t2) -> type' t1 t2
    (TEInst{}, _)          -> nope
    (TEApp t1, TEApp t2)   -> type' t1 t2
    (TEApp{}, _)           -> nope

  spine f sp1 sp2 = trace "unify spine" $ unless (length sp1 == length sp2) nope >> zipWithM_ f sp1 sp2

  sig c1 c2 = trace "unify sig" $ spine type' c1 c2

  solve v t = trace "solve" $ go []
    where
    go ext = onTop $ \ lvl (m :=: d ::: _K) -> case (m == v, occursIn (== TMetavar m) lvl t, d) of
      (True,  True,  _)       -> mismatch "infinite type" (Right (metavar m)) t
      (True,  False, Nothing) -> replace (ext ++ [ m :=: Just t ::: _K ])
      (True,  False, Just t') -> modify (<>< ext) >> type' t' t >> restore
      (False, True,  _)       -> go ((m :=: d ::: _K):ext) >> replace []
      (False, False, _)       -> go ext >> restore


-- Machinery

newtype Elab m a = Elab { runElab :: ReaderC ElabContext (FreshC (StateC Subst (StateC Context m))) a }
  deriving (Algebra (Reader ElabContext :+: Fresh :+: State Subst :+: State Context :+: sig), Applicative, Functor, Monad)

elabWith :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Reader Span) sig m => (Context -> a -> m b) -> Elab m a -> m b
elabWith k m = runState (\ ctx (_subst, a) -> k ctx a) Context.empty . runState (curry pure) mempty . evalFresh 0 $ do
  ctx <- mkContext
  runReader ctx . runElab $ m
  where
  mkContext = ElabContext <$> ask <*> ask <*> pure [] <*> ask <*> ask

elab :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Reader Span) sig m => Elab m a -> m a
elab = elabWith (const pure)

elabType :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Reader Span) sig m => Elab m TExpr -> m Type
elabType = elabWith (\ ctx t -> pure (evalIn ctx t))

elabTerm :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Reader Span) sig m => Elab m Expr -> m Value
elabTerm = elabWith (\ ctx e -> pure (uncurry E.eval (toEnv ctx) e))

elabSynth :: Has (Reader Graph :+: Reader MName :+: Reader Module :+: Reader Span) sig m => Elab m (Expr ::: Type) -> m (Value ::: Type)
elabSynth = elabWith (\ ctx (e ::: _T) -> let (subst, env) = toEnv ctx in pure (E.eval subst env e ::: T.eval subst env (T.quote 0 _T)))


check :: Has Trace sig m => (Check m a ::: Type) -> Elab m a
check (m ::: _T) = trace "check" $ runCheck m _T

newtype Check m a = Check { runCheck :: Type -> Elab m a }
  deriving (Applicative, Functor) via ReaderC Type (Elab m)

mapCheck :: (Elab m a -> Elab m b) -> Check m a -> Check m b
mapCheck f m = Check $ \ _T -> f (runCheck m _T)


newtype Synth m a = Synth { synth :: Elab m (a ::: Type) }

instance Functor (Synth m) where
  fmap f (Synth m) = Synth (first f <$> m)

mapSynth :: (Elab m (a ::: Type) -> Elab m (b ::: Type)) -> Synth m a -> Synth m b
mapSynth f = Synth . f . synth


bind :: Bind m a ::: ([Type], Type) -> Check m b -> Check m (a, b)
bind (p ::: (s, _T)) = runBind p s _T

newtype Bind m a = Bind { runBind :: forall x . [Type] -> Type -> Check m x -> Check m (a, x) }
  deriving (Functor)

mapBind :: (forall x . Elab m (a, x) -> Elab m (b, x)) -> Bind m a -> Bind m b
mapBind f m = Bind $ \ sig _A b -> mapCheck f (runBind m sig _A b)
