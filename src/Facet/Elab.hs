{-# LANGUAGE ScopedTypeVariables #-}
-- | This module defines the /elaboration/ of terms in 'S.Expr' into values in 'Type'.
--
-- Elaboration is the only way 'Type's are constructed from untrusted terms, and so typechecking is performed at this point. If elaboration succeeds and a 'Type' is returned, that 'Type' does not require further verification; hence, 'Type's elide source span information.
module Facet.Elab
( -- * General
  unify
, lookupInContext
, lookupInSig
, resolveQ
, resolveC
, meta
, (|-)
  -- * Errors
, pushSpan
, Err(..)
, ErrReason(..)
, err
, couldNotSynthesize
, resourceMismatch
, freeVariable
, expectMatch
, expectFunction
  -- * Warnings
, Warn(..)
, WarnReason(..)
, warn
  -- * Unification
, StaticContext(..)
, ElabContext(..)
, context_
, sig_
  -- * Machinery
, Elab(..)
, depth
, use
, extendSig
, runElabWith
, runElabType
, runElabTerm
, runElabSynth
, runElabSynthType
) where

import Control.Algebra
import Control.Applicative as Alt (Alternative(..))
import Control.Carrier.Error.Church
import Control.Carrier.Reader
import Control.Carrier.State.Church
import Control.Carrier.Writer.Church
import Control.Effect.Lens (views)
import Control.Lens (Lens', lens)
import Control.Monad (guard, unless)
import Data.Foldable (asum)
import Data.Semialign.Exts
import Facet.Context as Context
import Facet.Core.Module
import Facet.Core.Term as E
import Facet.Core.Type as T
import Facet.Effect.Write
import Facet.Graph as Graph
import Facet.Lens
import Facet.Name hiding (L, R)
import Facet.Semiring
import Facet.Snoc
import Facet.Source (Source, slice)
import Facet.Span (Span(..))
import Facet.Subst
import Facet.Syntax
import Facet.Usage as Usage
import Facet.Vars as Vars
import GHC.Stack
import Prelude hiding (span, zipWith)

-- TODO:
-- - clause/pattern matrices
-- - tacit (eta-reduced) definitions w/ effects
-- - mutual recursion? does this work already? who knows
-- - datatypes containing computations

-- General

-- FIXME: should we give metas names so we can report holes or pattern variables cleanly?
meta :: Has (State (Subst Type Type)) sig m => Type -> m Meta
meta _T = state (declareMeta @Type @Type _T)


resolveWith
  :: (HasCallStack, Has (Throw Err) sig m)
  => (forall m . (Alternative m, Monad m) => Name -> Module -> m (QName :=: x))
  -> QName
  -> Elab m (QName :=: x)
resolveWith lookup n = asks (\ StaticContext{ module', graph } -> lookupWith lookup graph module' n) >>= \case
  []  -> freeVariable n
  [v] -> pure v
  ds  -> ambiguousName n (map (\ (q :=: _) -> q) ds)

resolveC :: (HasCallStack, Has (Throw Err) sig m) => QName -> Elab m (QName :=: Maybe (Pos Expr) ::: Pos Type)
resolveC = resolveWith lookupC

resolveQ :: (HasCallStack, Has (Throw Err) sig m) => QName -> Elab m (QName :=: Def)
resolveQ = resolveWith lookupD

lookupInContext :: Alternative m => QName -> Context -> m (Index, Quantity, Type)
lookupInContext (m:.:n)
  | m == Nil  = lookupIndex n
  | otherwise = const Alt.empty

-- FIXME: probably we should instead look up the effect op globally, then check for membership in the sig
-- FIXME: this can’t differentiate between different instantiations of the same effect (i.e. based on type)
-- FIXME: return the index in the sig; it’s vital for evaluation of polymorphic effects when there are multiple such
lookupInSig :: (Alternative m, Monad m) => QName -> Module -> Graph -> [Interface Type] -> m (QName :=: Def)
lookupInSig (m :.: n) mod graph = fmap asum . fmap . (. getInterface) $ \case
  T.Ne (Global q@(m':.:_)) Nil -> do
    guard (m == Nil || m == m')
    defs <- interfaceScope =<< lookupQ graph mod q
    _ :=: d <- lookupScope n defs
    pure $ m':.:n :=: d
  _                            -> Alt.empty
  where
  interfaceScope (_ :=: d) = case d of { DInterface defs _ -> pure defs ; _ -> Alt.empty }


(|-) :: (HasCallStack, Has (Throw Err) sig m) => Binding -> Elab m a -> Elab m a
Binding n q _T |- b = do
  sigma <- asks scale
  d <- depth
  let exp = sigma >< q
  (u, a) <- censor (`Usage.withoutVars` Vars.singleton d) $ listen $ locally context_ (|> Binding n exp _T) b
  let act = Usage.lookup d u
  unless (act `sat` exp)
    $ resourceMismatch n exp act
  pure a

infix 1 |-

-- | Test whether the first quantity suffices to satisfy a requirement of the second.
sat :: Quantity -> Quantity -> Bool
sat a b
  | b == zero = a == b
  | b == one  = a == b
  | otherwise = True


depth :: Has (Reader ElabContext) sig m => m Level
depth = views context_ level

use :: Has (Reader ElabContext :+: Writer Usage) sig m => Index -> Quantity -> m ()
use i q = do
  d <- depth
  tell (Usage.singleton (indexToLevel d i) q)

extendSig :: Has (Reader ElabContext) sig m => [Interface Type] -> m a -> m a
extendSig = locally sig_ . (++)


-- Errors

pushSpan :: Has (Reader ElabContext) sig m => Span -> m a -> m a
pushSpan = locally spans_ . flip (:>)


data Err = Err
  { source    :: Source
  , reason    :: ErrReason
  , context   :: Context
  , subst     :: Subst Type Type
  , callStack :: CallStack
  }

data ErrReason
  = FreeVariable QName
  -- FIXME: add source references for the imports, definition sites, and any re-exports.
  | AmbiguousName QName [QName]
  | CouldNotSynthesize String
  | ResourceMismatch Name Quantity Quantity
  | Mismatch String (Either String Type) Type
  | Hole Name Type
  | Invariant String

instance Substitutable Err Type Type where
  applySubst subst e@Err{ reason, context } = e{ reason = reason' }
    where
    reason' = case reason of
      FreeVariable{}       -> reason
      AmbiguousName{}      -> reason
      CouldNotSynthesize{} -> reason
      ResourceMismatch{}   -> reason
      Mismatch m exp act   -> Mismatch m (roundtrip <$> exp) (roundtrip act)
      Hole n t             -> Hole n (roundtrip t)
      Invariant{}          -> reason
    env = toEnv context
    d = level context
    roundtrip = T.eval subst (Left <$> env) . T.quote d


-- FIXME: apply the substitution before showing this to the user
err :: (HasCallStack, Has (Throw Err) sig m) => ErrReason -> Elab m a
err reason = do
  StaticContext{ source } <- ask
  ElabContext{ context, spans } <- ask
  subst <- get
  throwError $ applySubst subst $ Err (maybe source (slice source) (peek spans)) reason context subst GHC.Stack.callStack

mismatch :: (HasCallStack, Has (Throw Err) sig m) => String -> Either String Type -> Type -> Elab m a
mismatch msg exp act = withFrozenCallStack $ err $ Mismatch msg exp act

couldNotUnify :: (HasCallStack, Has (Throw Err) sig m) => String -> Type -> Type -> Elab m a
couldNotUnify msg t1 t2 = withFrozenCallStack $ mismatch msg (Right t2) t1

couldNotSynthesize :: (HasCallStack, Has (Throw Err) sig m) => String -> Elab m a
couldNotSynthesize v = withFrozenCallStack $ err $ CouldNotSynthesize v

resourceMismatch :: (HasCallStack, Has (Throw Err) sig m) => Name -> Quantity -> Quantity -> Elab m a
resourceMismatch n exp act = withFrozenCallStack $ err $ ResourceMismatch n exp act

freeVariable :: (HasCallStack, Has (Throw Err) sig m) => QName -> Elab m a
freeVariable n = withFrozenCallStack $ err $ FreeVariable n

ambiguousName :: (HasCallStack, Has (Throw Err) sig m) => QName -> [QName] -> Elab m a
ambiguousName n qs = withFrozenCallStack $ err $ AmbiguousName n qs


-- Warnings

data Warn = Warn
  { source :: Source
  , reason :: WarnReason
  }

data WarnReason
  = RedundantCatchAll Name
  | RedundantVariable Name


warn :: Has (Write Warn) sig m => WarnReason -> Elab m ()
warn reason = do
  StaticContext{ source } <- ask
  ElabContext{ spans } <- ask
  write $ Warn (maybe source (slice source) (peek spans)) reason


-- Patterns

expectMatch :: (HasCallStack, Has (Throw Err) sig m) => (Type -> Maybe out) -> String -> String -> Type -> Elab m out
expectMatch pat exp s _T = maybe (mismatch s (Left exp) _T) pure (pat _T)

expectFunction :: (HasCallStack, Has (Throw Err) sig m) => String -> Type -> Elab m (Maybe Name ::: (Quantity, Type), Type)
expectFunction = expectMatch (\case{ Arrow n q t b -> pure (n ::: (q, t), b) ; _ -> Nothing }) "_ -> _"


-- Unification

-- | Context which doesn’t change during elaboration of a single term.
data StaticContext = StaticContext
  { graph   :: Graph
  , module' :: Module
  , source  :: Source
  , scale   :: Quantity
  }

data ElabContext = ElabContext
  { context :: Context
  , sig     :: [Interface Type]
  , spans   :: Snoc Span
  }

context_ :: Lens' ElabContext Context
context_ = lens (\ ElabContext{ context } -> context) (\ e context -> (e :: ElabContext){ context })

sig_ :: Lens' ElabContext [Interface Type]
sig_ = lens sig (\ e sig -> e{ sig })

spans_ :: Lens' ElabContext (Snoc Span)
spans_ = lens spans (\ e spans -> e{ spans })


-- FIXME: we don’t get good source references during unification
unify :: forall m sig . (HasCallStack, Has (Throw Err) sig m) => Type -> Type -> Elab m ()
unify t1 t2 = type' t1 t2
  where
  nope :: HasCallStack => Elab m a
  nope = couldNotUnify "mismatch" t1 t2

  type' :: HasCallStack => Type -> Type -> Elab m ()
  type' = curry $ \case
    (Ne (Metavar v1) Nil, Ne (Metavar v2) Nil) -> flexFlex v1 v2
    (Ne (Metavar v1) Nil, t2)                  -> solve v1 t2
    (t1, Ne (Metavar v2) Nil)                  -> solve v2 t1
    (Type, Type)                               -> pure ()
    (Type, _)                                  -> nope
    (Interface, Interface)                     -> pure ()
    (Interface, _)                             -> nope
    (ForAll n t1 b1, ForAll _ t2 b2)           -> type' t1 t2 >> depth >>= \ d -> Binding n zero t1 |- type' (b1 (free d)) (b2 (free d))
    (ForAll{}, _)                              -> nope
    (Arrow _ _ a1 b1, Arrow _ _ a2 b2)         -> type' a1 a2 >> type' b1 b2
    (Arrow{}, _)                               -> nope
    (Comp s1 t1, Comp s2 t2)                   -> sig s1 s2 >> type' t1 t2
    (Comp{}, _)                                -> nope
    (Ne v1 sp1, Ne v2 sp2)                     -> var v1 v2 >> spine type' sp1 sp2
    (Ne{}, _)                                  -> nope
    (String, String)                           -> pure ()
    (String, _)                                -> nope
    (Thunk t1, Thunk t2)                       -> type' t1 t2
    (Thunk{}, _)                               -> nope

  var :: (HasCallStack, Eq a) => Var Meta a -> Var Meta a -> Elab m ()
  var = curry $ \case
    (Global q1, Global q2)   -> unless (q1 == q2) nope
    (Global{}, _)            -> nope
    (Free v1, Free v2)       -> unless (v1 == v2) nope
    (Free{}, _)              -> nope
    (Metavar m1, Metavar m2) -> unless (m1 == m2) nope
    (Metavar{}, _)           -> nope

  spine :: (HasCallStack, Foldable t, Zip t) => (a -> b -> Elab m ()) -> t a -> t b -> Elab m ()
  spine f sp1 sp2 = unless (length sp1 == length sp2) nope >> zipWithM_ f sp1 sp2

  sig :: (HasCallStack, Foldable t, Zip t) => t (Interface Type) -> t (Interface Type) -> Elab m ()
  sig c1 c2 = spine type' (getInterface <$> c1) (getInterface <$> c2)

  flexFlex :: HasCallStack => Meta -> Meta -> Elab m ()
  flexFlex v1 v2
    | v1 == v2  = pure ()
    | otherwise = do
      (t1, t2) <- gets (\ s -> (lookupMeta v1 s, lookupMeta v2 s))
      case (t1, t2) of
        (Just t1, Just t2) -> type' (ty t1) (ty t2)
        (Just t1, Nothing) -> type' (metavar v2) (tm t1)
        (Nothing, Just t2) -> type' (metavar v1) (tm t2)
        (Nothing, Nothing) -> solve v1 (metavar v2)

  solve :: HasCallStack => Meta -> Type -> Elab m ()
  solve v t = do
    d <- depth
    if occursIn (== Metavar v) d t then
      mismatch "infinite type" (Right (metavar v)) t
    else
      gets (lookupMeta @Type @Type v) >>= \case
        Nothing          -> modify (solveMeta @Type @Type v t)
        Just (t' ::: _T) -> type' t' t


-- Machinery

newtype Elab m a = Elab { runElab :: ReaderC ElabContext (ReaderC StaticContext (WriterC Usage (StateC (Subst Type Type) m))) a }
  deriving (Algebra (Reader ElabContext :+: Reader StaticContext :+: Writer Usage :+: State (Subst Type Type) :+: sig), Applicative, Functor, Monad)

runElabWith :: Has (Reader Graph :+: Reader Module :+: Reader Source) sig m => Quantity -> (Subst Type Type -> a -> m b) -> Elab m a -> m b
runElabWith scale k m = runState k mempty . runWriter (const pure) $ do
  (graph, module', source) <- (,,) <$> ask <*> ask <*> ask
  let stat = StaticContext{ graph, module', source, scale }
      ctx  = ElabContext{ context = Context.empty, sig = [], spans = Nil }
  runReader stat . runReader ctx . runElab $ m

runElabType :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Elab m TExpr -> m Type
runElabType = runElabWith zero (\ subst t -> pure (T.eval subst Nil t))

runElabTerm :: Has (Reader Graph :+: Reader Module :+: Reader Source) sig m => Elab m a -> m a
runElabTerm = runElabWith one (const pure)

runElabSynth :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Quantity -> Elab m (a ::: Type) -> m (a ::: Type)
runElabSynth scale = runElabWith scale (\ subst (e ::: _T) -> pure (e ::: T.eval subst Nil (T.quote 0 _T)))

runElabSynthType :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Quantity -> Elab m (TExpr ::: Type) -> m (Type ::: Type)
runElabSynthType scale = runElabWith scale (\ subst (_T ::: _K) -> pure (T.eval subst Nil _T ::: T.eval subst Nil (T.quote 0 _K)))
