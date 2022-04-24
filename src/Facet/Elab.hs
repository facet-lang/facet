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
, resolveDef
, resolveC
, meta
, instantiate
, (|-)
, (||-)
  -- * Errors
, pushSpan
, withSpanC
, withSpan
, Err(..)
, ErrReason(..)
, _FreeVariable
, _AmbiguousName
, _UnifyType
, UnifyErrReason(..)
, _Mismatch
, _Occurs
, mismatchTypes
, mismatchKinds
, couldNotUnifyKinds
, couldNotSynthesize
, resourceMismatch
, freeVariable
, missingInterface
, assertMatch
, assertTypesMatch
, assertFunction
, ErrC(..)
  -- * Warnings
, Warn(..)
, WarnReason(..)
, warn
  -- * Unification
, ElabContext(..)
, context_
, sig_
  -- * Machinery
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
import           Control.Monad (unless)
import           Data.Foldable (for_)
import           Facet.Context hiding (empty)
import qualified Facet.Context as Context (empty)
import           Facet.Effect.Write
import qualified Facet.Env as Env
import           Facet.Functor.Check
import           Facet.Functor.Synth
import           Facet.Graph as Graph
import           Facet.Interface
import           Facet.Kind
import           Facet.Lens hiding (use, view)
import           Facet.Module
import           Facet.Name hiding (L, R)
import           Facet.Pattern
import           Facet.Quote
import           Facet.Semiring
import           Facet.Snoc
import           Facet.Snoc.NonEmpty (NonEmpty(..))
import           Facet.Source (Source, slice)
import           Facet.Span (Span(..))
import           Facet.Subst
import           Facet.Syntax hiding (context_)
import qualified Facet.Syntax as S
import           Facet.Term.Expr as E
import qualified Facet.Type.Expr as TX
import           Facet.Type.Norm as TN
import           Facet.Usage as Usage
import           Facet.Vars as Vars
import           Fresnel.Fold ((^?))
import           Fresnel.Ixed (ix)
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


instantiate :: Has (State (Subst Type)) sig m => (a -> TX.Type -> a) -> a ::: Type -> m (a ::: Type)
instantiate inst = go
  where
  go (e ::: _T) = case _T of
    TN.ForAll _ _T _B -> do
      m <- meta _T
      go (inst e (TX.Var (Free (Left m))) ::: _B (metavar m))
    _                 -> pure $ e ::: _T


resolveWith
  :: (Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m)
  => (forall sig m . Has (Choose :+: Empty) sig m => Name -> Module -> m d)
  -> QName
  -> m d
resolveWith lookup n = ask >>= \ graph -> asks (\ module' -> lookupWith lookup graph module' n) >>= \case
  []  -> freeVariable n
  [v] -> pure v
  _   -> ambiguousName n

resolveC :: (Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m) => QName -> m (QName :=: Type)
resolveC = resolveWith lookupConstructor

resolveDef :: (Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m) => QName -> m Def
resolveDef = resolveWith lookupDef

lookupInContext :: Has (Choose :+: Empty) sig m => QName -> Context -> m (LName Index, Either Kind Type)
lookupInContext (m:|>n)
  | m == Nil  = lookupIndex n
  | otherwise = const empty

-- FIXME: probably we should instead look up the effect op globally, then check for membership in the sig
-- FIXME: return the index in the sig; it’s vital for evaluation of polymorphic effects when there are multiple such
lookupInSig :: Has (Choose :+: Empty) sig m => QName -> Module -> Graph -> [Signature Type] -> m (QName :=: Type)
lookupInSig (m :|> n) mod graph = foldMapC $ foldMapC (\ (Interface q@(m':|>_) _) -> do
  guard (m == Nil || m == m')
  defs <- interfaceScope =<< lookupQ graph mod q
  d <- maybe empty pure (defs ^? ix n)
  pure $ m' :|> n :=: d) . interfaces
  where
  interfaceScope = \case { DSubmodule (SInterface defs) _K -> pure defs ; _ -> empty }


(|-) :: Has (Reader ElabContext :+: Throw ErrReason :+: Writer Usage) sig m => (Quantity, Pattern (Name :==> Type)) -> m a -> m a
(q, p) |- b = do
  d <- depth
  (u, a) <- censor (`Usage.withoutVars` Vars.singleton d) $ listen $ locally context_ (|> Type p) b
  for_ p $ \ (n :==> _T) -> do
    let exp = q
        act = Usage.lookup (LName d n) u
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

depth :: Has (Reader ElabContext) sig m => m Level
depth = views context_ level

use :: Has (Reader ElabContext :+: Writer Usage) sig m => LName Index -> Quantity -> m ()
use n q = do
  d <- depth
  tell (Usage.singleton (toLeveled d n) q)


-- Errors

pushSpan :: Has (Reader ElabContext) sig m => Span -> m a -> m a
pushSpan = locally spans_ . flip (:>)

withSpanC :: Has (Reader ElabContext) sig m => S.Ann a -> (a -> Type <==: m b) -> Type <==: m b
withSpanC (S.Ann s _ a) k = Check (\ _T -> pushSpan s (k a <==: _T))

withSpan :: Has (Reader ElabContext) sig m => (a -> m b) -> S.Ann a -> m b
withSpan k (S.Ann s _ a) = pushSpan s (k a)



data Err = Err
  { source    :: Source
  , reason    :: ErrReason
  , context   :: Context
  , subst     :: Subst Type
  , sig       :: [Signature Type]
  , callStack :: CallStack
  }

-- FIXME: not all of these need contexts/metacontexts.
data ErrReason
  = FreeVariable QName
  -- FIXME: add source references for the imports, definition sites, and any re-exports.
  | AmbiguousName QName
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

_AmbiguousName :: Prism' ErrReason QName
_AmbiguousName = prism' AmbiguousName (\case
  AmbiguousName n -> Just n
  _               -> Nothing)

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

applySubst :: Context -> Subst Type -> ErrReason -> ErrReason
applySubst ctx subst r = case r of
  FreeVariable{}       -> r
  AmbiguousName{}      -> r
  CouldNotSynthesize{} -> r
  ResourceMismatch{}   -> r
  -- NB: not substituting in @r@ because we want to retain the cyclic occurrence (and finitely)
  UnifyType r exp act  -> UnifyType r (fmap roundtrip <$> exp) (roundtrip <$> act)
  UnifyKind{}          -> r
  Hole n t             -> Hole n (roundtrip t)
  Invariant{}          -> r
  MissingInterface i   -> MissingInterface (roundtrip <$> i)
  where
  roundtrip = apply subst (toEnv ctx)


mismatchTypes :: Has (Throw ErrReason) sig m => Exp (Either String Type) -> Act Type -> m a
mismatchTypes exp act = withFrozenCallStack $ throwError $ UnifyType Mismatch exp act

mismatchKinds :: Has (Throw ErrReason) sig m => Exp (Either String Kind) -> Act Kind -> m a
mismatchKinds exp act = withFrozenCallStack $ throwError $ UnifyKind exp act

couldNotUnifyKinds :: Has (Throw ErrReason) sig m => Exp Kind -> Act Kind -> m a
couldNotUnifyKinds t1 t2 = withFrozenCallStack $ mismatchKinds (Right <$> t1) t2

couldNotSynthesize :: Has (Throw ErrReason) sig m => m a
couldNotSynthesize = withFrozenCallStack $ throwError CouldNotSynthesize

resourceMismatch :: Has (Throw ErrReason) sig m => Name -> Quantity -> Quantity -> m a
resourceMismatch n exp act = withFrozenCallStack $ throwError $ ResourceMismatch n exp act

freeVariable :: Has (Throw ErrReason) sig m => QName -> m a
freeVariable n = withFrozenCallStack $ throwError $ FreeVariable n

-- FIXME: get references for the resolved names
ambiguousName :: Has (Throw ErrReason) sig m => QName -> m a
ambiguousName n = withFrozenCallStack $ throwError $ AmbiguousName n

missingInterface :: Has (Throw ErrReason) sig m => Interface Type -> m a
missingInterface i = withFrozenCallStack $ throwError $ MissingInterface i


newtype ErrC m a = ErrC { runErr :: m a }
  deriving (Applicative, Functor, Monad)

instance (Has (Reader ElabContext) sig m, Has (Reader Source) sig m, Has (State (Subst Type)) sig m, Has (Throw Err) sig m) => Algebra (Throw ErrReason :+: sig) (ErrC m) where
  alg hdl sig ctx = case sig of
    L (Throw reason) -> do
      source <- ask
      ElabContext{ context, sig, spans } <- ask
      subst <- get
      throwError $ Err (maybe source (slice source) (peek spans)) (applySubst context subst reason) context subst sig GHC.Stack.callStack
    R other     -> ErrC (alg (runErr . hdl) other ctx)


-- Warnings

data Warn = Warn
  { source :: Source
  , reason :: WarnReason
  }

data WarnReason
  = RedundantCatchAll Name
  | RedundantVariable Name


warn :: (Has (Reader ElabContext) sig m, Has (Reader Source) sig m, Has (Write Warn) sig m) => WarnReason -> m ()
warn reason = do
  source <- ask
  ElabContext{ spans } <- ask
  write $ Warn (maybe source (slice source) (peek spans)) reason


-- Patterns

assertMatch :: Applicative m => (Exp (Either String b) -> Act s -> m a) -> Prism' s a -> String -> s -> m a
assertMatch mismatch pat exp _T = maybe (mismatch (Exp (Left exp)) (Act _T)) pure (_T ^? pat)

assertTypesMatch :: Has (Throw ErrReason) sig m => Prism' Type a -> String -> Type -> m a
assertTypesMatch pat exp _T = maybe (mismatchTypes (Exp (Left exp)) (Act _T)) pure (_T ^? pat)

assertFunction :: Has (Throw ErrReason) sig m => Type -> m (Maybe Name, Quantity, Type, Type)
assertFunction = assertTypesMatch _Arrow "_ -> _"


-- Unification

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

elabWith :: (Subst Type -> a -> m b) -> ReaderC ElabContext (WriterC Usage (StateC (Subst Type) m)) a -> m b
elabWith k m = runState k mempty . runWriter (const pure) $ do
  let ctx  = ElabContext{ context = Context.empty, sig = mempty, spans = Nil }
  runReader ctx m

elabKind :: Applicative m => ReaderC ElabContext (WriterC Usage (StateC (Subst Type) m)) Kind -> m Kind
elabKind = elabWith (const pure)

elabType :: (HasCallStack, Applicative m) => ReaderC ElabContext (WriterC Usage (StateC (Subst Type) m)) TX.Type -> m Type
elabType = elabWith (\ subst t -> pure (TN.eval subst Env.empty t))

elabTerm :: Applicative m => ReaderC ElabContext (WriterC Usage (StateC (Subst Type) m)) Term -> m Term
elabTerm = elabWith (const pure)

elabSynthTerm :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => ReaderC ElabContext (WriterC Usage (StateC (Subst Type) m)) (Term :==> Type) -> m (Term :==> Type)
elabSynthTerm = elabWith (\ subst (e :==> _T) -> pure (e :==> TN.eval subst Env.empty (runQuoter 0 (quote _T))))

elabSynthType :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => ReaderC ElabContext (WriterC Usage (StateC (Subst Type) m)) (TX.Type :==> Kind) -> m (Type :==> Kind)
elabSynthType = elabWith (\ subst (_T :==> _K) -> pure (TN.eval subst Env.empty _T :==> _K))
