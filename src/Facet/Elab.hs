{-# LANGUAGE ScopedTypeVariables #-}
-- | This module defines the /elaboration/ of terms in 'S.Expr' into values in 'Type'.
--
-- Elaboration is the only way 'Type's are constructed from untrusted terms, and so typechecking is performed at this point. If elaboration succeeds and a 'Type' is returned, that 'Type' does not require further verification; hence, 'Type's elide source span information.
module Facet.Elab
( -- * General
  unifyN
, unifyP
, lookupInContext
, lookupInSig
, resolveQ
, resolveC
, meta
, (|-)
  -- * Errors
, pushSpan
, Err(..)
, ErrType(..)
, ErrReason(..)
, err
, couldNotUnify
, couldNotSynthesize
, resourceMismatch
, freeVariable
, assertKind
, assertNType
, assertPType
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
, runElabWith
, runElabKind
, runElabType
, runElabTerm
, runElabSynth
, runElabSynthKind
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
import Facet.Context as Context
import Facet.Core.Module
import Facet.Core.Term as E
import Facet.Core.Type as T
import Facet.Effect.Write
import Facet.Graph as Graph
import Facet.Lens
import Facet.Name hiding (L, R)
import Facet.Semialign
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
meta :: Has (State (Subst PType Kind)) sig m => Kind -> m Meta
meta _T = state (declareMeta @Kind @PType _T)


resolveWith
  :: (HasCallStack, Has (Throw Err) sig m)
  => (forall m . (Alternative m, Monad m) => Name -> Module -> m (QName :=: x))
  -> QName
  -> Elab m (QName :=: x)
resolveWith lookup n = asks (\ StaticContext{ module', graph } -> lookupWith lookup graph module' n) >>= \case
  []  -> freeVariable n
  [v] -> pure v
  ds  -> ambiguousName n (map (\ (q :=: _) -> q) ds)

resolveC :: (HasCallStack, Has (Throw Err) sig m) => QName -> Elab m (QName :=: Maybe PExpr ::: PType)
resolveC = resolveWith lookupC

resolveQ :: (HasCallStack, Has (Throw Err) sig m) => QName -> Elab m (QName :=: Def)
resolveQ = resolveWith lookupD

lookupInContext :: Alternative m => QName -> Context -> m (Index, Quantity, Sorted)
lookupInContext (m:.:n)
  | m == Nil  = lookupIndex n
  | otherwise = const Alt.empty

-- FIXME: probably we should instead look up the effect op globally, then check for membership in the sig
-- FIXME: this can’t differentiate between different instantiations of the same effect (i.e. based on type)
-- FIXME: return the index in the sig; it’s vital for evaluation of polymorphic effects when there are multiple such
lookupInSig :: (Alternative m, Monad m) => QName -> Module -> Graph -> [Interface] -> m (QName :=: Def)
lookupInSig (m :.: n) mod graph = fmap asum . fmap . (. getInterface) $ \case
  KSpine q@(m':.:_) _ -> do
    guard (m == Nil || m == m')
    defs <- fmap tm . unDInterface . def =<< lookupQ graph mod q
    _ :=: d <- lookupScope n defs
    pure $ m':.:n :=: d
  _                   -> Alt.empty


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


-- Errors

pushSpan :: Has (Reader ElabContext) sig m => Span -> m a -> m a
pushSpan = locally spans_ . flip (:>)


data Err = Err
  { source    :: Source
  , reason    :: ErrReason
  , context   :: Context
  , subst     :: Subst PType Kind
  , callStack :: CallStack
  }

data ErrType
  = EK Kind
  | EN NType
  | EP PType

data ErrReason
  = FreeVariable QName
  -- FIXME: add source references for the imports, definition sites, and any re-exports.
  | AmbiguousName QName [QName]
  | CouldNotSynthesize String
  | ResourceMismatch Name Quantity Quantity
  | Mismatch (Either String ErrType) ErrType
  | Hole Name ErrType
  | Invariant String

instance Substitutable Err PType Kind where
  applySubst subst e@Err{ reason, context } = e{ reason = reason' }
    where
    reason' = case reason of
      FreeVariable{}       -> reason
      AmbiguousName{}      -> reason
      CouldNotSynthesize{} -> reason
      ResourceMismatch{}   -> reason
      Mismatch exp act     -> Mismatch (applyErrType <$> exp) (applyErrType act)
      Hole n t             -> Hole n (applyErrType t)
      Invariant{}          -> reason
    env = toEnv context
    d = level context
    applyErrType = \case
      EN ty -> EN (roundtripN ty)
      EP ty -> EP (roundtripP ty)
      EK ki -> EK ki -- FIXME: can/should we substitute in this?
    roundtripP = T.evalP subst (Left <$> env) . T.quoteP d
    roundtripN = T.evalN subst (Left <$> env) . T.quoteN d


-- FIXME: apply the substitution before showing this to the user
err :: (HasCallStack, Has (Throw Err) sig m) => ErrReason -> Elab m a
err reason = do
  StaticContext{ source } <- ask
  ElabContext{ context, spans } <- ask
  subst <- get
  throwError $ applySubst subst $ Err (maybe source (slice source) (peek spans)) reason context subst GHC.Stack.callStack

mismatch :: (HasCallStack, Has (Throw Err) sig m) => Either String ErrType -> ErrType -> Elab m a
mismatch exp act = withFrozenCallStack $ err $ Mismatch exp act

couldNotUnify :: (HasCallStack, Has (Throw Err) sig m) => ErrType -> ErrType -> Elab m a
couldNotUnify t1 t2 = withFrozenCallStack $ mismatch (Right t2) t1

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

assertKind :: (HasCallStack, Has (Throw Err) sig m) => (Kind -> Maybe out) -> String -> String -> Kind -> Elab m out
assertKind pat exp _ _T = withFrozenCallStack $ maybe (mismatch (Left exp) (EK _T)) pure (pat _T)

assertNType :: (HasCallStack, Has (Throw Err) sig m) => (NType -> Maybe out) -> String -> String -> NType -> Elab m out
assertNType pat exp _ _T = withFrozenCallStack $ maybe (mismatch (Left exp) (EN _T)) pure (pat _T)

assertPType :: (HasCallStack, Has (Throw Err) sig m) => (PType -> Maybe out) -> String -> String -> PType -> Elab m out
assertPType pat exp _ _T = withFrozenCallStack $ maybe (mismatch (Left exp) (EP _T)) pure (pat _T)


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
  , sig     :: [Interface]
  , spans   :: Snoc Span
  }

context_ :: Lens' ElabContext Context
context_ = lens (\ ElabContext{ context } -> context) (\ e context -> (e :: ElabContext){ context })

sig_ :: Lens' ElabContext [Interface]
sig_ = lens sig (\ e sig -> e{ sig })

spans_ :: Lens' ElabContext (Snoc Span)
spans_ = lens spans (\ e spans -> e{ spans })


-- FIXME: we don’t get good source references during unification
unifyN :: forall m sig . (HasCallStack, Has (Throw Err) sig m) => NType -> NType -> Elab m ()
unifyN = fst unify

unifyP :: forall m sig . (HasCallStack, Has (Throw Err) sig m) => PType -> PType -> Elab m ()
unifyP = snd unify

unify :: forall m sig . (HasCallStack, Has (Throw Err) sig m) => (NType -> NType -> Elab m (), PType -> PType -> Elab m ())
unify = (ntype, ptype)
  where
  ntype :: HasCallStack => NType -> NType -> Elab m ()
  ntype t1 t2 = case (t1, t2) of
    (Arrow _ _ a1 b1, Arrow _ _ a2 b2) -> ptype a1 a2 >> ntype b1 b2
    (Arrow{}, _)                       -> nope
    (Comp s1 t1, Comp s2 t2)           -> sigOr nope s1 s2 >> ptype t1 t2
    (Comp{}, _)                        -> nope
    where
    nope :: HasCallStack => Elab m a
    nope = couldNotUnify (EN t1) (EN t2)

  ptype :: HasCallStack => PType -> PType -> Elab m ()
  ptype t1 t2 = case (t1, t2) of
    (ForAll n t1 b1, ForAll _ t2 b2)           -> kind t1 t2 >> depth >>= \ d -> Binding n zero (SType t1) |- ptype (b1 (free d)) (b2 (free d))
    (ForAll{}, _)                              -> nope
    (Ne (Metavar v1) Nil, Ne (Metavar v2) Nil) -> flexFlex v1 v2
    (Ne (Metavar v1) Nil, t2)                  -> solve v1 t2
    (t1, Ne (Metavar v2) Nil)                  -> solve v2 t1
    (Ne v1 sp1, Ne v2 sp2)                     -> var v1 v2 >> spineOr nope ptype sp1 sp2
    (Ne{}, _)                                  -> nope
    (String, String)                           -> pure ()
    (String, _)                                -> nope
    (Thunk t1, Thunk t2)                       -> ntype t1 t2
    (Thunk{}, _)                               -> nope
    where
    nope :: HasCallStack => Elab m a
    nope = couldNotUnify (EP t1) (EP t2)

  kind t1 t2 = unless (t1 == t2) (couldNotUnify (EK t1) (EK t2))

  var :: HasCallStack => Var Meta Level -> Var Meta Level -> Elab m ()
  var v1 v2 = case (v1, v2) of
    (Global q1, Global q2)   -> unless (q1 == q2) nope
    (Global{}, _)            -> nope
    (Free v1, Free v2)       -> unless (v1 == v2) nope
    (Free{}, _)              -> nope
    (Metavar m1, Metavar m2) -> unless (m1 == m2) nope
    (Metavar{}, _)           -> nope
    where
    nope :: HasCallStack => Elab m a
    nope = couldNotUnify (EP (Ne v1 Nil)) (EP (Ne v2 Nil))

  spineOr :: (Foldable t, Zip t) => Elab m () -> (a -> b -> Elab m ()) -> t a -> t b -> Elab m ()
  spineOr nope f sp1 sp2 = unless (length sp1 == length sp2) nope >> zipWithM_ f sp1 sp2

  sigOr :: (Foldable t, Zip t) => Elab m () -> t Interface -> t Interface -> Elab m ()
  sigOr nope c1 c2 = spineOr nope kind (getInterface <$> c1) (getInterface <$> c2)

  flexFlex :: HasCallStack => Meta -> Meta -> Elab m ()
  flexFlex v1 v2
    | v1 == v2  = pure ()
    | otherwise = do
      (t1, t2) <- gets (\ s -> (lookupMeta @PType @Kind v1 s, lookupMeta v2 s))
      case (t1, t2) of
        (Just t1, Just t2) -> ptype (tm t1) (tm t2)
        (Just t1, Nothing) -> ptype (metavar v2) (tm t1)
        (Nothing, Just t2) -> ptype (metavar v1) (tm t2)
        (Nothing, Nothing) -> solve v1 (metavar v2)

  solve :: HasCallStack => Meta -> PType -> Elab m ()
  solve v t = do
    d <- depth
    if occursInP v d t then
      mismatch (Right (EP (metavar v))) (EP t) -- FIXME: use a specialized error rather than mismatch
    else
      gets (lookupMeta @PType @Kind v) >>= \case
        Nothing          -> modify (solveMeta @PType @Kind v t)
        Just (t' ::: _T) -> ptype t' t


-- Machinery

newtype Elab m a = Elab { runElab :: ReaderC ElabContext (ReaderC StaticContext (WriterC Usage (StateC (Subst PType Kind) m))) a }
  deriving (Algebra (Reader ElabContext :+: Reader StaticContext :+: Writer Usage :+: State (Subst PType Kind) :+: sig), Applicative, Functor, Monad)

runElabWith :: Has (Reader Graph :+: Reader Module :+: Reader Source) sig m => Quantity -> (Subst PType Kind -> a -> m b) -> Elab m a -> m b
runElabWith scale k m = runState k mempty . runWriter (const pure) $ do
  (graph, module', source) <- (,,) <$> ask <*> ask <*> ask
  let stat = StaticContext{ graph, module', source, scale }
      ctx  = ElabContext{ context = Context.empty, sig = [], spans = Nil }
  runReader stat . runReader ctx . runElab $ m

runElabKind :: Has (Reader Graph :+: Reader Module :+: Reader Source) sig m => Elab m Kind -> m Kind
runElabKind = runElabWith zero (\ _ t -> pure t) -- FIXME: we should substitute in the kind

runElabType :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Elab m PTExpr -> m PType
runElabType = runElabWith zero (\ subst t -> pure (T.evalP subst Nil t))

runElabTerm :: Has (Reader Graph :+: Reader Module :+: Reader Source) sig m => Elab m a -> m a
runElabTerm = runElabWith one (const pure)

runElabSynth :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Quantity -> Elab m (a ::: PType) -> m (a ::: PType)
runElabSynth scale = runElabWith scale (\ subst (e ::: _T) -> pure (e ::: T.evalP subst Nil (T.quoteP 0 _T)))

runElabSynthKind :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Quantity -> Elab m (PTExpr ::: Kind) -> m (PType ::: Kind)
runElabSynthKind scale = runElabWith scale (\ subst (_T ::: _K) -> pure (T.evalP subst Nil _T ::: _K)) -- FIXME: we should substitute in the kind as well
