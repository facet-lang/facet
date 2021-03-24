{-# LANGUAGE ScopedTypeVariables #-}
-- | This module defines the /elaboration/ of terms in 'S.Expr' into values in 'Type'.
--
-- Elaboration is the only way 'Type's are constructed from untrusted terms, and so typechecking is performed at this point. If elaboration succeeds and a 'Type' is returned, that 'Type' does not require further verification; hence, 'Type's elide source span information.
module Facet.Elab
( -- * General
  lookupInContext
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
, UnifyErrReason(..)
, err
, couldNotUnify
, occursCheckFailure
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
, Exp(..)
, Act(..)
  -- * Machinery
, Elab(..)
, evalTExpr
, depth
, use
, elabWith
, elabKind
, elabType
, elabTerm
, elabSynthTerm
, elabSynthType
) where

import           Control.Algebra
import           Control.Carrier.Empty.Church
import           Control.Carrier.Error.Church
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Carrier.Writer.Church
import           Control.Effect.Choose
import           Control.Effect.Lens (views)
import           Control.Lens (Lens', lens)
import           Control.Monad (unless)
import           Facet.Context hiding (empty)
import qualified Facet.Context as Context (empty)
import           Facet.Core.Module
import           Facet.Core.Term as E
import           Facet.Core.Type as T
import           Facet.Effect.Write
import           Facet.Graph as Graph
import           Facet.Lens
import           Facet.Name hiding (L, R)
import           Facet.Semiring
import           Facet.Snoc
import           Facet.Snoc.NonEmpty (toSnoc)
import           Facet.Source (Source, slice)
import           Facet.Span (Span(..))
import           Facet.Syntax
import           Facet.Usage as Usage
import           Facet.Vars as Vars
import           GHC.Stack
import           Prelude hiding (span, zipWith)

-- TODO:
-- - clause/pattern matrices
-- - tacit (eta-reduced) definitions w/ effects
-- - mutual recursion? does this work already? who knows
-- - datatypes containing computations

-- General

-- FIXME: should we give metas names so we can report holes or pattern variables cleanly?
meta :: Has (State Subst) sig m => Kind -> m Meta
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
  => (forall sig m . Has (Choose :+: Empty) sig m => Name -> Module -> m (RName :=: d))
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

lookupInContext :: Has (Choose :+: Empty) sig m => QName -> Context -> m (Index, Quantity, Either Kind Type)
lookupInContext (m:.n)
  | m == Nil  = lookupIndex n
  | otherwise = const empty

-- FIXME: probably we should instead look up the effect op globally, then check for membership in the sig
-- FIXME: return the index in the sig; it’s vital for evaluation of polymorphic effects when there are multiple such
lookupInSig :: Has (Choose :+: Empty) sig m => QName -> Module -> Graph -> [Interface Type] -> m (RName :=: Def)
lookupInSig (m :. n) mod graph = foldMapC $ \ (Interface q@(m':.:_) _) -> do
  guard (m == Nil || m == toSnoc m')
  defs <- interfaceScope =<< lookupQ graph mod (toQ q)
  _ :=: d <- lookupScope n defs
  pure $ m':.:n :=: d
  where
  interfaceScope (_ :=: d) = case d of { DInterface defs _K -> pure defs ; _ -> empty }


(|-) :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State Subst :+: Throw Err :+: Writer Usage) sig m) => Binding -> m a -> m a
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


evalTExpr :: Has (Reader ElabContext :+: State Subst) sig m => TExpr -> m Type
evalTExpr texpr = T.eval <$> get <*> views context_ (fmap Left . toEnv) <*> pure texpr

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
  , subst     :: Subst
  , callStack :: CallStack
  }

data ErrReason
  = FreeVariable QName
  -- FIXME: add source references for the imports, definition sites, and any re-exports.
  | AmbiguousName QName [RName]
  | CouldNotSynthesize
  | ResourceMismatch Name Quantity Quantity
  | Unify UnifyErrReason (Exp (Either String Subject)) (Act Subject)
  | Hole Name Subject
  | Invariant String

data UnifyErrReason
  = Mismatch
  | Occurs Meta Subject

applySubst :: Context -> Subst -> ErrReason -> ErrReason
applySubst ctx subst r = case r of
  FreeVariable{}       -> r
  AmbiguousName{}      -> r
  CouldNotSynthesize{} -> r
  ResourceMismatch{}   -> r
  -- NB: not substituting in @r@ because we want to retain the cyclic occurrence (and finitely)
  Unify r exp act      -> Unify r (fmap roundtripS <$> exp) (roundtripS <$> act)
  Hole n t             -> Hole n (roundtripS t)
  Invariant{}          -> r
  where
  env = toEnv ctx
  d = level ctx
  roundtripS = \case
    SK k -> SK k
    ST k -> ST $ roundtrip k
  roundtrip = T.eval subst (Left <$> env) . T.quote d


-- FIXME: apply the substitution before showing this to the user
err :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State Subst :+: Throw Err) sig m) => ErrReason -> m a
err reason = do
  StaticContext{ source } <- ask
  ElabContext{ context, spans } <- ask
  subst <- get
  throwError $ Err (maybe source (slice source) (peek spans)) (applySubst context subst reason) context subst GHC.Stack.callStack

mismatch :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State Subst :+: Throw Err) sig m) => Exp (Either String Subject) -> Act Subject -> m a
mismatch exp act = withFrozenCallStack $ err $ Unify Mismatch exp act

couldNotUnify :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State Subst :+: Throw Err) sig m) => Exp Subject -> Act Subject -> m a
couldNotUnify t1 t2 = withFrozenCallStack $ mismatch (Right <$> t1) t2

occursCheckFailure :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State Subst :+: Throw Err) sig m) => Meta -> Subject -> Exp Subject -> Act Subject -> m a
occursCheckFailure m v exp act = withFrozenCallStack $ err $ Unify (Occurs m v) (Right <$> exp) act

couldNotSynthesize :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State Subst :+: Throw Err) sig m) => m a
couldNotSynthesize = withFrozenCallStack $ err CouldNotSynthesize

resourceMismatch :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State Subst :+: Throw Err) sig m) => Name -> Quantity -> Quantity -> m a
resourceMismatch n exp act = withFrozenCallStack $ err $ ResourceMismatch n exp act

freeVariable :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State Subst :+: Throw Err) sig m) => QName -> m a
freeVariable n = withFrozenCallStack $ err $ FreeVariable n

ambiguousName :: (HasCallStack, Has (Reader ElabContext :+: Reader StaticContext :+: State Subst :+: Throw Err) sig m) => QName -> [RName] -> m a
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

assertMatch :: (HasCallStack, Has (Throw Err) sig m) => (Subject -> Maybe out) -> String -> Subject -> Elab m out
assertMatch pat exp _T = maybe (mismatch (Exp (Left exp)) (Act _T)) pure (pat _T)

assertFunction :: (HasCallStack, Has (Throw Err) sig m) => Type -> Elab m (Maybe Name ::: (Quantity, Type), Type)
assertFunction = assertMatch (\case{ ST (VArrow n q t b) -> pure (n ::: (q, t), b) ; _ -> Nothing }) "_ -> _" . ST


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


newtype Exp a = Exp { getExp :: a }
  deriving (Functor)

newtype Act a = Act { getAct :: a }
  deriving (Functor)


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

elabSynthType :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Elab m (TExpr ::: Kind) -> m (Type ::: Kind)
elabSynthType = elabWith zero (\ subst (_T ::: _K) -> pure (T.eval subst Nil _T ::: _K))
