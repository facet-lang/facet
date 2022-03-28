{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
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
, (||-)
  -- * Errors
, pushSpan
-- , Err(..)
, ErrReason(..)
, _FreeVariable
, _AmbiguousName
, _UnifyType
, UnifyErrReason(..)
, _Mismatch
, _Occurs
, err
, makeErr
, mismatchTypes
, mismatchKinds
, couldNotUnifyKinds
, couldNotSynthesize
, resourceMismatch
, freeVariable
, missingInterface
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
import           Control.Monad (unless, (<=<))
import           Data.Foldable (for_)
import           Facet.Context hiding (empty)
import qualified Facet.Context as Context (empty)
import           Facet.Effect.Write
import qualified Facet.Env as Env
import           Facet.Functor.Synth
import           Facet.Graph as Graph
import           Facet.Interface
import           Facet.Kind
import           Facet.Lens hiding (use)
import           Facet.Module
import           Facet.Name hiding (L, R)
import           Facet.Pattern
import           Facet.Quote
import           Facet.Semiring
import           Facet.Snoc
import           Facet.Snoc.NonEmpty (toSnoc)
import           Facet.Source (Source, slice)
import           Facet.Span (Span(..))
import           Facet.Subst
import           Facet.Syntax hiding (context_)
import           Facet.Term.Expr as E
import qualified Facet.Type.Expr as TX
import           Facet.Type.Norm as TN
import           Facet.Usage as Usage
import           Facet.Vars as Vars
import           Fresnel.Fold ((^?))
import           Fresnel.Lens (Lens', lens)
import           Fresnel.Prism (Prism', prism')
import           GHC.Stack
import           Prelude hiding (span, zipWith)

-- TODO:
-- - clause/pattern matrices
-- - tacit (eta-reduced) definitions w/ effects
-- - mutual recursion? does this work already? who knows
-- - datatypes containing computations

-- General

-- FIXME: should we give metas names so we can report holes or pattern variables cleanly?
meta :: Has (State (Subst Type)) sig m => Kind -> m Meta
meta _T = state (declareMeta @Type)


instantiate :: Algebra sig m => (a -> TX.Type -> a) -> a ::: Type -> Elab m (a ::: Type)
instantiate inst = go
  where
  go (e ::: _T) = case _T of
    TN.ForAll _ _T _B -> do
      m <- meta _T
      go (inst e (TX.Var (Free (Left m))) ::: _B (metavar m))
    _                 -> pure $ e ::: _T


resolveWith
  :: (Has (Reader ElabContext) sig m, Has (Reader StaticContext) sig m, Has (Throw ErrReason) sig m)
  => (forall sig m . Has (Choose :+: Empty) sig m => Name -> Module -> m (RName :=: d))
  -> QName
  -> m (RName :=: d)
resolveWith lookup n = asks (\ StaticContext{ module', graph } -> lookupWith lookup graph module' n) >>= \case
  []  -> freeVariable n
  [v] -> pure v
  ds  -> ambiguousName n (map nm ds)

resolveC :: (Has (Reader ElabContext) sig m, Has (Reader StaticContext) sig m, Has (Throw ErrReason) sig m) => QName -> m (RName :=: Maybe Term ::: Type)
resolveC = resolveWith lookupC

resolveQ :: (Has (Reader ElabContext) sig m, Has (Reader StaticContext) sig m, Has (Throw ErrReason) sig m) => QName -> m (RName :=: Def)
resolveQ = resolveWith lookupD

lookupInContext :: Has (Choose :+: Empty) sig m => QName -> Context -> m (LName Index, Either Kind (Quantity, Type))
lookupInContext (m:.n)
  | m == Nil  = lookupIndex n
  | otherwise = const empty

-- FIXME: probably we should instead look up the effect op globally, then check for membership in the sig
-- FIXME: return the index in the sig; it’s vital for evaluation of polymorphic effects when there are multiple such
lookupInSig :: Has (Choose :+: Empty) sig m => QName -> Module -> Graph -> [Signature Type] -> m (RName :=: Type)
lookupInSig (m :. n) mod graph = foldMapC $ foldMapC (\ (Interface q@(m':.:_) _) -> do
  guard (m == Nil || m == toSnoc m')
  defs <- interfaceScope =<< lookupQ graph mod (toQ q)
  _ :=: d <- lookupScope n defs
  pure $ m':.:n :=: d) . interfaces
  where
  interfaceScope (_ :=: d) = case d of { DSubmodule (SInterface defs) _K -> pure defs ; _ -> empty }


(|-) :: Has (Reader ElabContext :+: Throw ErrReason :+: Writer Usage) sig m => (Quantity, Pattern (Name :==> Type)) -> m a -> m a
(q, p) |- b = do
  d <- depth
  (u, a) <- censor (`Usage.withoutVars` Vars.singleton (getUsed d)) $ listen $ locally context_ (|> Type q id p) b
  for_ p $ \ (n :==> _T) -> do
    let exp = q
        act = Usage.lookup (LName (getUsed d) n) u
    unless (act `sat` exp)
      $ resourceMismatch n exp act
  pure a

infix 1 |-

(||-) :: Has (Reader ElabContext) sig m => (Name :==> Kind) -> m a -> m a
k ||- b = locally context_ (|> Kind k) b

infix 1 ||-

-- | Test whether the first quantity suffices to satisfy a requirement of the second.
sat :: Quantity -> Quantity -> Bool
sat a b
  | b == zero = a == b
  | b == one  = a == b
  | otherwise = True


evalTExpr :: Has (Reader ElabContext :+: State (Subst Type)) sig m => TX.Type -> m Type
evalTExpr texpr = TN.eval <$> get <*> views context_ toEnv <*> pure texpr

depth :: Has (Reader ElabContext) sig m => m Used
depth = views context_ level

use :: Has (Reader ElabContext :+: Writer Usage) sig m => LName Index -> Quantity -> m ()
use n q = do
  d <- depth
  tell (Usage.singleton (toLeveled d n) q)


-- Errors

pushSpan :: Has (Reader ElabContext) sig m => Span -> m a -> m a
pushSpan = locally spans_ . flip (:>)


-- data Err = Err
--   { source    :: Source
--   , reason    :: ErrReason
--   , context   :: Context
--   , subst     :: Subst Type
--   , sig       :: [Signature Type]
--   , callStack :: CallStack
--   }

-- FIXME: not all of these need contexts/metacontexts.
data ErrReason
  = FreeVariable QName
  -- FIXME: add source references for the imports, definition sites, and any re-exports.
  | AmbiguousName QName [RName]
  | CouldNotSynthesize
  | ResourceMismatch Name Quantity Quantity
  | UnifyType UnifyErrReason (Exp (Either String Type)) (Act Type)
  | UnifyKind (Exp (Either String Kind)) (Act Kind)
  | Hole Name Type
  | Invariant String
  | MissingInterface (Interface Type)

_FreeVariable :: Prism' ErrReason QName
_FreeVariable = prism' FreeVariable (\case
  FreeVariable n -> Just n
  _              -> Nothing)

_AmbiguousName :: Prism' ErrReason (QName, [RName])
_AmbiguousName = prism' (uncurry AmbiguousName) (\case
  AmbiguousName n ns -> Just (n, ns)
  _                  -> Nothing)

_UnifyType :: Prism' ErrReason (UnifyErrReason, Exp (Either String Type), Act Type)
_UnifyType = prism' (\ (r, x, a) -> UnifyType r x a) (\case
  UnifyType r x a -> Just (r, x, a)
  _               -> Nothing)

data UnifyErrReason
  = Mismatch
  | Occurs Meta Type

_Mismatch :: Prism' UnifyErrReason ()
_Mismatch = prism' (const Mismatch) (\case
  Mismatch -> Just ()
  _        -> Nothing)

_Occurs :: Prism' UnifyErrReason (Meta, Type)
_Occurs = prism' (uncurry Occurs) (\case
  Occurs v c -> Just (v, c)
  _          -> Nothing)

-- applySubst :: Context -> Subst Type -> ErrReason -> ErrReason
-- applySubst ctx subst r = case r of
--   FreeVariable{}       -> r
--   AmbiguousName{}      -> r
--   CouldNotSynthesize{} -> r
--   ResourceMismatch{}   -> r
--   -- NB: not substituting in @r@ because we want to retain the cyclic occurrence (and finitely)
--   UnifyType r exp act  -> UnifyType r (fmap roundtrip <$> exp) (roundtrip <$> act)
--   UnifyKind{}          -> r
--   Hole n t             -> Hole n (roundtrip t)
--   Invariant{}          -> r
--   MissingInterface i   -> MissingInterface (roundtrip <$> i)
--   where
--   roundtrip = apply subst (toEnv ctx)


err :: Has (Throw ErrReason) sig m => ErrReason -> m a
err = throwError <=< makeErr

makeErr :: Has (Throw ErrReason) sig m => ErrReason -> m ErrReason
makeErr = pure
-- makeErr reason = do
--   StaticContext{ source } <- ask
--   ElabContext{ context, sig, spans } <- ask
--   subst <- get
--   pure $ Err (maybe source (slice source) (peek spans)) (applySubst context subst reason) context subst sig GHC.Stack.callStack

mismatchTypes :: Has (Throw ErrReason) sig m => Exp (Either String Type) -> Act Type -> m a
mismatchTypes exp act = withFrozenCallStack $ err $ UnifyType Mismatch exp act

mismatchKinds :: Has (Throw ErrReason) sig m => Exp (Either String Kind) -> Act Kind -> m a
mismatchKinds exp act = withFrozenCallStack $ err $ UnifyKind exp act

couldNotUnifyKinds :: Has (Throw ErrReason) sig m => Exp Kind -> Act Kind -> m a
couldNotUnifyKinds t1 t2 = withFrozenCallStack $ mismatchKinds (Right <$> t1) t2

couldNotSynthesize :: Has (Throw ErrReason) sig m => m a
couldNotSynthesize = withFrozenCallStack $ err CouldNotSynthesize

resourceMismatch :: Has (Throw ErrReason) sig m => Name -> Quantity -> Quantity -> m a
resourceMismatch n exp act = withFrozenCallStack $ err $ ResourceMismatch n exp act

freeVariable :: Has (Throw ErrReason) sig m => QName -> m a
freeVariable n = withFrozenCallStack $ err $ FreeVariable n

ambiguousName :: Has (Throw ErrReason) sig m => QName -> [RName] -> m a
ambiguousName n qs = withFrozenCallStack $ err $ AmbiguousName n qs

missingInterface :: Has (Throw ErrReason) sig m => Interface Type -> m a
missingInterface i = withFrozenCallStack $ err $ MissingInterface i


newtype ErrC m a = ErrC { runErr :: m a }
  deriving (Applicative, Functor, Monad)

instance Has (Throw ErrReason) sig m => Algebra (Throw ErrReason :+: sig) (ErrC m) where
  alg hdl sig ctx = case sig of
    L (Throw e) -> err e
    R other     -> ErrC (alg (runErr . hdl) other ctx)


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

assertMatch :: (Exp (Either String b) -> Act s -> Elab m a) -> Prism' s a -> String -> s -> Elab m a
assertMatch mismatch pat exp _T = maybe (mismatch (Exp (Left exp)) (Act _T)) pure (_T ^? pat)

assertFunction :: Has (Throw ErrReason) sig m => Type -> Elab m (Maybe Name, Quantity, Type, Type)
assertFunction = assertMatch mismatchTypes _Arrow "_ -> _"


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
  , sig     :: [Signature Type]
  , spans   :: Snoc Span
  }

context_ :: Lens' ElabContext Context
context_ = lens (\ ElabContext{ context } -> context) (\ ElabContext{ sig, spans } context -> ElabContext{ context, sig, spans })

sig_ :: Lens' ElabContext [Signature Type]
sig_ = lens (\ ElabContext{ sig } -> sig) (\ ElabContext{ context, spans } sig -> ElabContext{ context, sig, spans })

spans_ :: Lens' ElabContext (Snoc Span)
spans_ = lens spans (\ e spans -> e{ spans })


-- Machinery

newtype Elab m a = Elab { runElab :: ReaderC ElabContext (ReaderC StaticContext (WriterC Usage (StateC (Subst Type) m))) a }
  deriving (Algebra (Reader ElabContext :+: Reader StaticContext :+: Writer Usage :+: State (Subst Type) :+: sig), Applicative, Functor, Monad)

elabWith :: Has (Reader Graph :+: Reader Module :+: Reader Source) sig m => Quantity -> (Subst Type -> a -> m b) -> Elab m a -> m b
elabWith scale k m = runState k mempty . runWriter (const pure) $ do
  (graph, module', source) <- (,,) <$> ask <*> ask <*> ask
  let stat = StaticContext{ graph, module', source, scale }
      ctx  = ElabContext{ context = Context.empty, sig = mempty, spans = Nil }
  runReader stat . runReader ctx . runElab $ m

elabKind :: Has (Reader Graph :+: Reader Module :+: Reader Source) sig m => Elab m Kind -> m Kind
elabKind = elabWith zero (const pure)

elabType :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Elab m TX.Type -> m Type
elabType = elabWith zero (\ subst t -> pure (TN.eval subst Env.empty t))

elabTerm :: Has (Reader Graph :+: Reader Module :+: Reader Source) sig m => Elab m Term -> m Term
elabTerm = elabWith one (const pure)

elabSynthTerm :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Elab m (Term :==> Type) -> m (Term :==> Type)
elabSynthTerm = elabWith one (\ subst (e :==> _T) -> pure (e :==> TN.eval subst Env.empty (runQuoter 0 (quote _T))))

elabSynthType :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => Elab m (TX.Type :==> Kind) -> m (Type :==> Kind)
elabSynthType = elabWith zero (\ subst (_T :==> _K) -> pure (TN.eval subst Env.empty _T :==> _K))
