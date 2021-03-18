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
, instantiate
, (|-)
  -- * Errors
, pushSpan
, Err(..)
, ErrReason(..)
, err
, couldNotUnify
, couldNotSynthesize
, resourceMismatch
, freeVariable
, assertMatch
, assertFunction
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
, elabWith
, elabKind
, elabType
, elabTerm
, elabSynthTerm
, elabSynthType
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
import Facet.Snoc.NonEmpty (toSnoc)
import Facet.Source (Source, slice)
import Facet.Span (Span(..))
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
meta :: Has (State Subst) sig m => Type -> m Meta
meta _T = state (declareMeta _T)


instantiate :: Algebra sig m => (a -> TExpr -> a) -> a ::: Type -> Elab m (a ::: Type)
instantiate inst = go
  where
  go (e ::: _T) = case _T of
    VForAll _ _T _B -> do
      m <- meta _T
      go (inst e (TVar (Free (Left m))) ::: _B (metavar m))
    _                -> pure $ e ::: _T


resolveWith
  :: (HasCallStack, Has (Throw Err) sig m)
  => (forall m . Alternative m => Name -> Module -> m (RName :=: d))
  -> QName
  -> Elab m (RName :=: d)
resolveWith lookup n = asks (\ StaticContext{ module', graph } -> lookupWith lookup graph module' n) >>= \case
  []  -> freeVariable n
  [v] -> pure v
  ds  -> ambiguousName n (map (\ (q :=: _) -> q) ds)

resolveC :: (HasCallStack, Has (Throw Err) sig m) => QName -> Elab m (RName :=: Maybe Expr ::: Type)
resolveC = resolveWith lookupC

resolveQ :: (HasCallStack, Has (Throw Err) sig m) => QName -> Elab m (RName :=: Def)
resolveQ = resolveWith lookupD

lookupInContext :: Alternative m => QName -> Context -> m (Index, Quantity, Either Kind Type)
lookupInContext (m:.n)
  | m == Nil  = lookupIndex n
  | otherwise = const Alt.empty

-- FIXME: probably we should instead look up the effect op globally, then check for membership in the sig
-- FIXME: return the index in the sig; it’s vital for evaluation of polymorphic effects when there are multiple such
lookupInSig :: (Alternative m, Monad m) => QName -> Module -> Graph -> [Type] -> m (RName :=: Def)
lookupInSig (m :. n) mod graph = fmap asum . fmap $ \case
  VNe (Global q@(m':.:_)) _ _ -> do
    guard (m == Nil || m == toSnoc m')
    defs <- interfaceScope =<< lookupQ graph mod (toQ q)
    _ :=: d <- lookupScope n defs
    pure $ m':.:n :=: d
  _                             -> Alt.empty
  where
  interfaceScope (_ :=: d) = case d of { DInterface defs _K -> pure defs ; _ -> Alt.empty }


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

extendSig :: Has (Reader ElabContext) sig m => [Type] -> m a -> m a
extendSig = locally sig_ . (++)


-- Errors

pushSpan :: Has (Reader ElabContext) sig m => Span -> m a -> m a
pushSpan = locally spans_ . flip (:>)


data Err = Err
  { source    :: Source
  , reason    :: ErrReason
  , context   :: Context
  , subst     :: Subst
  , callStack :: CallStack
  }

data ErrReason
  = FreeVariable QName
  -- FIXME: add source references for the imports, definition sites, and any re-exports.
  | AmbiguousName QName [RName]
  | CouldNotSynthesize String
  | ResourceMismatch Name Quantity Quantity
  | Mismatch (Either String (Either Kind Type)) (Either Kind Type)
  | Hole Name Type
  | Invariant String

applySubst :: Context -> Subst -> ErrReason -> ErrReason
applySubst ctx subst r = case r of
  FreeVariable{}       -> r
  AmbiguousName{}      -> r
  CouldNotSynthesize{} -> r
  ResourceMismatch{}   -> r
  Mismatch exp act     -> Mismatch (fmap roundtrip <$> exp) (roundtrip <$> act)
  Hole n t             -> Hole n (roundtrip t)
  Invariant{}          -> r
  where
  env = toEnv ctx
  d = level ctx
  roundtrip = T.eval subst (Left <$> env) . T.quote d


-- FIXME: apply the substitution before showing this to the user
err :: (HasCallStack, Has (Throw Err) sig m) => ErrReason -> Elab m a
err reason = do
  StaticContext{ source } <- ask
  ElabContext{ context, spans } <- ask
  subst <- get
  throwError $ Err (maybe source (slice source) (peek spans)) (applySubst context subst reason) context subst GHC.Stack.callStack

mismatch :: (HasCallStack, Has (Throw Err) sig m) => Either String (Either Kind Type) -> Either Kind Type -> Elab m a
mismatch exp act = withFrozenCallStack $ err $ Mismatch exp act

couldNotUnify :: (HasCallStack, Has (Throw Err) sig m) => Either Kind Type -> Either Kind Type -> Elab m a
couldNotUnify t1 t2 = withFrozenCallStack $ mismatch (Right t2) t1

couldNotSynthesize :: (HasCallStack, Has (Throw Err) sig m) => String -> Elab m a
couldNotSynthesize v = withFrozenCallStack $ err $ CouldNotSynthesize v

resourceMismatch :: (HasCallStack, Has (Throw Err) sig m) => Name -> Quantity -> Quantity -> Elab m a
resourceMismatch n exp act = withFrozenCallStack $ err $ ResourceMismatch n exp act

freeVariable :: (HasCallStack, Has (Throw Err) sig m) => QName -> Elab m a
freeVariable n = withFrozenCallStack $ err $ FreeVariable n

ambiguousName :: (HasCallStack, Has (Throw Err) sig m) => QName -> [RName] -> Elab m a
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

assertMatch :: (HasCallStack, Has (Throw Err) sig m) => (Either Kind Type -> Maybe out) -> String -> Either Kind Type -> Elab m out
assertMatch pat exp _T = maybe (mismatch (Left exp) _T) pure (pat _T)

assertFunction :: (HasCallStack, Has (Throw Err) sig m) => Type -> Elab m (Maybe Name ::: (Quantity, Type), Type)
assertFunction = assertMatch (\case{ Right (VArrow n q t b) -> pure (n ::: (q, t), b) ; _ -> Nothing }) "_ -> _" . Right


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
  , sig     :: [Type]
  , spans   :: Snoc Span
  }

context_ :: Lens' ElabContext Context
context_ = lens (\ ElabContext{ context } -> context) (\ e context -> (e :: ElabContext){ context })

sig_ :: Lens' ElabContext [Type]
sig_ = lens sig (\ e sig -> e{ sig })

spans_ :: Lens' ElabContext (Snoc Span)
spans_ = lens spans (\ e spans -> e{ spans })


-- FIXME: we don’t get good source references during unification
unify :: (HasCallStack, Has (Throw Err) sig m) => Type -> Type -> Elab m ()
unify t1 t2 = type' t1 t2
  where
  nope = couldNotUnify (Right t1) (Right t2)

  type' = curry $ \case
    (VNe (Free (Left v1)) Nil Nil, VNe (Free (Left v2)) Nil Nil) -> flexFlex v1 v2
    (VNe (Free (Left v1)) Nil Nil, t2)                           -> solve v1 t2
    (t1, VNe (Free (Left v2)) Nil Nil)                           -> solve v2 t1
    (VType, VType)                                               -> pure ()
    (VType, _)                                                   -> nope
    (VInterface, VInterface)                                     -> pure ()
    (VInterface, _)                                              -> nope
    (VForAll n t1 b1, VForAll _ t2 b2)                           -> type' t1 t2 >> depth >>= \ d -> Binding n zero (Right t1) |- type' (b1 (T.free d)) (b2 (T.free d))
    (VForAll{}, _)                                               -> nope
    -- FIXME: this must unify the signatures
    (VArrow _ _ a1 b1, VArrow _ _ a2 b2)                         -> type' a1 a2 >> type' b1 b2
    (VArrow{}, _)                                                -> nope
    (VComp s1 t1, VComp s2 t2)                                   -> sig s1 s2 >> type' t1 t2
    (VComp _ t1, t2)                                             -> type' t1 t2
    (t1, VComp _ t2)                                             -> type' t1 t2
    (VNe v1 ts1 sp1, VNe v2 ts2 sp2)                             -> var v1 v2 >> spine type' ts1 ts2 >> spine type' sp1 sp2
    (VNe{}, _)                                                   -> nope
    (VString, VString)                                           -> pure ()
    (VString, _)                                                 -> nope

  var = curry $ \case
    (Global q1, Global q2)             -> unless (q1 == q2) nope
    (Global{}, _)                      -> nope
    (Free (Right v1), Free (Right v2)) -> unless (v1 == v2) nope
    (Free (Left m1), Free (Left m2))   -> unless (m1 == m2) nope
    (Free{}, _)                        -> nope

  spine f sp1 sp2 = unless (length sp1 == length sp2) nope >> zipWithM_ f sp1 sp2

  sig c1 c2 = spine type' c1 c2

  flexFlex v1 v2
    | v1 == v2  = pure ()
    | otherwise = gets (\ s -> (T.lookupMeta v1 s, T.lookupMeta v2 s)) >>= \case
      (Just t1, Just t2) -> type' (tm t1) (tm t2)
      (Just t1, Nothing) -> type' (metavar v2) (tm t1)
      (Nothing, Just t2) -> type' (metavar v1) (tm t2)
      (Nothing, Nothing) -> solve v1 (metavar v2)

  solve v t = do
    d <- depth
    if occursIn (== Free (Left v)) d t then
      mismatch (Right (Right (metavar v))) (Right t)
    else
      gets (T.lookupMeta v) >>= \case
        Nothing          -> modify (T.solveMeta v t)
        Just (t' ::: _T) -> type' t' t


-- Machinery

newtype Elab m a = Elab { runElab :: ReaderC ElabContext (ReaderC StaticContext (WriterC Usage (StateC Subst m))) a }
  deriving (Algebra (Reader ElabContext :+: Reader StaticContext :+: Writer Usage :+: State Subst :+: sig), Applicative, Functor, Monad)

elabWith :: Has (Reader Graph :+: Reader Module :+: Reader Source) sig m => Quantity -> (Subst -> a -> m b) -> Elab m a -> m b
elabWith scale k m = runState k mempty . runWriter (const pure) $ do
  (graph, module', source) <- (,,) <$> ask <*> ask <*> ask
  let stat = StaticContext{ graph, module', source, scale }
      ctx  = ElabContext{ context = Context.empty, sig = [], spans = Nil }
  runReader stat . runReader ctx . runElab $ m

elabKind :: Has (Reader Graph :+: Reader Module :+: Reader Source) sig m => Elab m Kind -> m Kind
elabKind = elabWith zero (const pure)

elabType :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Elab m TExpr -> m Type
elabType = elabWith zero (\ subst t -> pure (T.eval subst Nil t))

elabTerm :: Has (Reader Graph :+: Reader Module :+: Reader Source) sig m => Elab m Expr -> m Expr
elabTerm = elabWith one (const pure)

elabSynthTerm :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Elab m (Expr ::: Type) -> m (Expr ::: Type)
elabSynthTerm = elabWith one (\ subst (e ::: _T) -> pure (e ::: T.eval subst Nil (T.quote 0 _T)))

elabSynthType :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Elab m (TExpr ::: Type) -> m (Type ::: Type)
elabSynthType = elabWith zero (\ subst (_T ::: _K) -> pure (T.eval subst Nil _T ::: T.eval subst Nil (T.quote 0 _K)))
