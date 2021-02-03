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
, pushSpan
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
, context_
, sig_
  -- * Machinery
, Elab(..)
, depth
, extendSig
, elabWith
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
import Control.Carrier.Reader
import Control.Carrier.State.Church
import Control.Effect.Empty
import Control.Effect.Lens (views)
import Control.Lens (Lens', lens)
import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.Foldable (asum)
import Data.Maybe (fromMaybe)
import Data.Semialign.Exts
import Facet.Context as Context
import Facet.Core.Module
import Facet.Core.Term as E
import Facet.Core.Type as T
import Facet.Effect.Write
import Facet.Graph as Graph
import Facet.Lens
import Facet.Name hiding (L, R)
import Facet.Semiring (zero)
import Facet.Source (Source(..))
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
meta :: Has (State Subst) sig m => Type -> m Meta
meta _T = state (declareMeta _T)


-- FIXME: does instantiation need to be guided by the expected type?
instantiate :: Algebra sig m => (a -> TExpr -> a) -> a ::: Type -> Elab m (a ::: Type)
instantiate inst = go
  where
  go (e ::: _T) = case _T of
    VTForAll _ _T _B -> do
      m <- meta _T
      go (inst e (TVar (TMetavar m)) ::: _B (metavar m))
    _                -> pure $ e ::: _T


switch :: (HasCallStack, Has (Throw Err) sig m) => Synth m a -> Check m a
switch (Synth m) = Check $ \ _K -> m >>= \ (a ::: _K') -> a <$ unify _K' _K

as :: (HasCallStack, Algebra sig m) => Check m Expr ::: Check m TExpr -> Synth m Expr
as (m ::: _T) = Synth $ do
  env <- views context_ toEnv
  subst <- get
  _T' <- T.eval subst (Left <$> env) <$> check (_T ::: VKType)
  a <- check (m ::: _T')
  pure $ a ::: _T'

resolveWith
  :: (HasCallStack, Has (Throw Err) sig m)
  => (forall m . Alternative m => Name -> Module -> m (Q Name :=: Maybe Def ::: Type))
  -> Q Name
  -> Elab m (Q Name :=: Maybe Def ::: Type)
resolveWith lookup n = asks (\ ElabContext{ module', graph } -> lookupWith lookup graph module' n) >>= \case
  []  -> freeVariable n
  [v] -> pure v
  ds  -> ambiguousName n (map (\ (q :=: _ ::: _) -> q) ds)

resolveC :: (HasCallStack, Has (Throw Err) sig m) => Q Name -> Elab m (Q Name :=: Maybe Def ::: Type)
resolveC = resolveWith lookupC

resolveQ :: (HasCallStack, Has (Throw Err) sig m) => Q Name -> Elab m (Q Name :=: Maybe Def ::: Type)
resolveQ = resolveWith lookupD

lookupInContext :: Q Name -> Context -> Maybe (Index, Type)
lookupInContext (m:.:n)
  | m == Nil  = lookupIndex n
  | otherwise = const Nothing

-- FIXME: probably we should instead look up the effect op globally, then check for membership in the sig
lookupInSig :: Q Name -> Module -> Graph -> [Type] -> Maybe (Q Name ::: Type)
lookupInSig (m :.: n) mod graph = fmap asum . fmap $ \case
  VTNe (TGlobal q@(m':.:_)) _ _ -> do
    guard (m == Nil || m == m')
    _ :=: Just (DInterface defs) ::: _ <- lookupQ graph mod q
    _ :=: _ ::: _T <- lookupScope n defs
    pure $ m':.:n ::: _T
  _                             -> Nothing


hole :: (HasCallStack, Has (Throw Err) sig m) => Name -> Check m a
hole n = Check $ \ _T -> withFrozenCallStack $ err $ Hole n _T

app :: (HasCallStack, Has (Throw Err) sig m) => (a -> b -> c) -> Synth m a -> Check m b -> Synth m c
app mk f a = Synth $ do
  f' ::: _F <- synth f
  (m ::: _A, _B) <- expectFunction "in application" _F
  a' <- either (const id) extendSig m $ check (a ::: _A)
  pure $ mk f' a' ::: _B


(|-) :: Algebra sig m => Binding -> Elab m a -> Elab m a
t |- b = locally context_ (|> t) b

infix 1 |-


depth :: Has (Reader ElabContext) sig m => m Level
depth = views context_ level

extendSig :: Has (Reader ElabContext) sig m => [Type] -> m a -> m a
extendSig = locally sig_ . (++)


-- Errors

pushSpan :: Has (Reader ElabContext) sig m => Span -> m a -> m a
pushSpan = locally spans_ . flip (:>)


data Err = Err
  { span      :: Span
  , reason    :: ErrReason
  , context   :: Context
  , subst     :: Subst
  , callStack :: CallStack
  }

data ErrReason
  = FreeVariable (Q Name)
  -- FIXME: add source references for the imports, definition sites, and any re-exports.
  | AmbiguousName (Q Name) [Q Name]
  | CouldNotSynthesize String
  | Mismatch String (Either String Type) Type
  | Hole Name Type
  | Invariant String

applySubst :: Context -> Subst -> ErrReason -> ErrReason
applySubst ctx subst r = case r of
  FreeVariable{}       -> r
  AmbiguousName{}      -> r
  CouldNotSynthesize{} -> r
  Mismatch m exp act   -> Mismatch m (roundtrip <$> exp) (roundtrip act)
  Hole n t             -> Hole n (roundtrip t)
  Invariant{}          -> r
  where
  env = toEnv ctx
  d = level ctx
  roundtrip = T.eval subst (Left <$> env) . T.quote d


-- FIXME: apply the substitution before showing this to the user
err :: (HasCallStack, Has (Throw Err) sig m) => ErrReason -> Elab m a
err reason = do
  ElabContext{ context, source = Source{ span }, spans } <- ask
  subst <- get
  throwError $ Err (fromMaybe span (peek spans)) (applySubst context subst reason) context subst GHC.Stack.callStack

mismatch :: (HasCallStack, Has (Throw Err) sig m) => String -> Either String Type -> Type -> Elab m a
mismatch msg exp act = withFrozenCallStack $ err $ Mismatch msg exp act

couldNotUnify :: (HasCallStack, Has (Throw Err) sig m) => String -> Type -> Type -> Elab m a
couldNotUnify msg t1 t2 = withFrozenCallStack $ mismatch msg (Right t2) t1

couldNotSynthesize :: (HasCallStack, Has (Throw Err) sig m) => String -> Elab m a
couldNotSynthesize v = withFrozenCallStack $ err $ CouldNotSynthesize v

freeVariable :: (HasCallStack, Has (Throw Err) sig m) => Q Name -> Elab m a
freeVariable n = withFrozenCallStack $ err $ FreeVariable n

ambiguousName :: (HasCallStack, Has (Throw Err) sig m) => Q Name -> [Q Name] -> Elab m a
ambiguousName n qs = withFrozenCallStack $ err $ AmbiguousName n qs


-- Warnings

data Warn = Warn
  { span   :: Maybe Span
  , reason :: WarnReason
  }

data WarnReason
  = RedundantCatchAll Name
  | RedundantVariable Name


warn :: Has (Write Warn) sig m => WarnReason -> Elab m ()
warn reason = do
  ElabContext{ spans } <- ask
  write $ Warn (peek spans) reason


-- Patterns

expectMatch :: (HasCallStack, Has (Throw Err) sig m) => (Type -> Maybe out) -> String -> String -> Type -> Elab m out
expectMatch pat exp s _T = maybe (mismatch s (Left exp) _T) pure (pat _T)

expectFunction :: (HasCallStack, Has (Throw Err) sig m) => String -> Type -> Elab m (Either Name [Type] ::: Type, Type)
expectFunction = expectMatch (\case{ VTArrow n t b -> pure (n ::: t, b) ; _ -> Nothing }) "_ -> _"


-- Unification

data ElabContext = ElabContext
  { graph   :: Graph
  , module' :: Module
  , source  :: Source
  , context :: Context
  , sig     :: [Type]
  , spans   :: Stack Span
  }

context_ :: Lens' ElabContext Context
context_ = lens (\ ElabContext{ context } -> context) (\ e context -> (e :: ElabContext){ context })

sig_ :: Lens' ElabContext [Type]
sig_ = lens sig (\ e sig -> e{ sig })

spans_ :: Lens' ElabContext (Stack Span)
spans_ = lens spans (\ e spans -> e{ spans })


-- FIXME: we don’t get good source references during unification
unify :: (HasCallStack, Has (Throw Err) sig m) => Type -> Type -> Elab m ()
unify t1 t2 = type' t1 t2
  where
  nope = couldNotUnify "mismatch" t1 t2

  type' = curry $ \case
    (VTNe (TMetavar v1) Nil Nil, VTNe (TMetavar v2) Nil Nil) -> flexFlex v1 v2
    (VTNe (TMetavar v1) Nil Nil, t2)                         -> solve v1 t2
    (t1, VTNe (TMetavar v2) Nil Nil)                         -> solve v2 t1
    (VKType, VKType)                                         -> pure ()
    (VKType, _)                                              -> nope
    (VKInterface, VKInterface)                               -> pure ()
    (VKInterface, _)                                         -> nope
    (VTForAll n t1 b1, VTForAll _ t2 b2)                     -> type' t1 t2 >> depth >>= \ d -> Binding n zero t1 |- type' (b1 (T.free d)) (b2 (T.free d))
    (VTForAll{}, _)                                          -> nope
    (VTArrow _ a1 b1, VTArrow _ a2 b2)                       -> type' a1 a2 >> type' b1 b2
    (VTArrow{}, _)                                           -> nope
    (VTComp s1 t1, VTComp s2 t2)                             -> sig s1 s2 >> type' t1 t2
    (VTComp{}, _)                                            -> nope
    (VTNe v1 ts1 sp1, VTNe v2 ts2 sp2)                       -> var v1 v2 >> spine type' ts1 ts2 >> spine type' sp1 sp2
    (VTNe{}, _)                                              -> nope
    (VTString, VTString)                                     -> pure ()
    (VTString, _)                                            -> nope

  var = curry $ \case
    (TGlobal q1, TGlobal q2)   -> unless (q1 == q2) nope
    (TGlobal{}, _)             -> nope
    (TFree v1, TFree v2)       -> unless (v1 == v2) nope
    (TFree{}, _)               -> nope
    (TMetavar m1, TMetavar m2) -> unless (m1 == m2) nope
    (TMetavar{}, _)            -> nope

  spine f sp1 sp2 = unless (length sp1 == length sp2) nope >> zipWithM_ f sp1 sp2

  sig c1 c2 = spine type' c1 c2

  flexFlex v1 v2
    | v1 == v2  = pure ()
    | otherwise = do
      (t1, t2) <- gets (\ s -> (T.lookupMeta v1 s, T.lookupMeta v2 s))
      case (t1, t2) of
        (Just t1, Just t2) -> type' (ty t1) (ty t2)
        (Just t1, Nothing) -> type' (metavar v2) (tm t1)
        (Nothing, Just t2) -> type' (metavar v1) (tm t2)
        (Nothing, Nothing) -> solve v1 (metavar v2)

  solve v t = do
    d <- depth
    if occursIn (== TMetavar v) d t then
      mismatch "infinite type" (Right (metavar v)) t
    else
      gets (T.lookupMeta v) >>= \case
        Nothing          -> modify (T.solveMeta v t)
        Just (t' ::: _T) -> type' t' t


-- Machinery

newtype Elab m a = Elab { runElab :: ReaderC ElabContext (StateC Subst m) a }
  deriving (Algebra (Reader ElabContext :+: State Subst :+: sig), Applicative, Functor, Monad)

elabWith :: Has (Reader Graph :+: Reader Module :+: Reader Source) sig m => (Subst -> a -> m b) -> Elab m a -> m b
elabWith k m = runState k mempty $ do
  ctx <- mkContext
  runReader ctx . runElab $ m
  where
  mkContext = ElabContext <$> ask <*> ask <*> ask <*> pure Context.empty <*> pure [] <*> pure Nil

elabType :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Elab m TExpr -> m Type
elabType = elabWith (\ subst t -> pure (T.eval subst Nil t))

elabTerm :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Elab m Expr -> m Value
elabTerm = elabWith (\ subst e -> pure (E.eval subst Nil e))

elabSynth :: Has (Reader Graph :+: Reader Module :+: Reader Source) sig m => Elab m (Expr ::: Type) -> m (Value ::: Type)
elabSynth = elabWith (\ subst (e ::: _T) -> pure (E.eval subst Nil e ::: T.eval subst Nil (T.quote 0 _T)))


check :: (Check m a ::: Type) -> Elab m a
check (m ::: _T) = runCheck m _T

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
