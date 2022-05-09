{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
-- | This module defines the /elaboration/ of terms in 'S.Expr' into values in 'Type'.
--
-- Elaboration is the only way 'Type's are constructed from untrusted terms, and so typechecking is performed at this point. If elaboration succeeds and a 'Type' is returned, that 'Type' does not require further verification; hence, 'Type's elide source span information.
module Facet.Elab
( -- * General
  lookupInContext
, lookupInTypeContext
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
, typeContext_
, sig_
  -- * Machinery
, evalTExpr
, depth
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
import           Control.Effect.Choose
import           Facet.Context hiding (empty)
import qualified Facet.Context as Context (empty)
import           Facet.Effect.Write
import           Facet.Functor.Check
import           Facet.Functor.Synth
import           Facet.Graph as Graph
import           Facet.Interface
import           Facet.Kind
import           Facet.Lens hiding (use, view)
import           Facet.Module
import           Facet.Name hiding (L, R)
import           Facet.Quote
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
import qualified Facet.TypeContext as TypeContext
import           Fresnel.Fold ((^?))
import           Fresnel.Getter (view)
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
      go (inst e (TX.Var (Bound (Left m))) ::: _B (metavar m))
    _                 -> pure $ e ::: _T


resolveWith
  :: (Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m)
  => (forall sig m . Has (Choose :+: Empty) sig m => Name -> Module -> m d)
  -> (d -> QName)
  -> QName
  -> m d
resolveWith lookup toQName n = ask >>= \ graph -> asks (\ module' -> lookupWith lookup graph module' n) >>= \case
  []  -> freeVariable n
  [v] -> pure v
  ns  -> ambiguousName n (map toQName ns)

resolveC :: (Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m) => QName -> m (QName :=: Type)
resolveC = resolveWith lookupConstructor (view tm_)

resolveDef :: (Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m) => QName -> m Def
resolveDef = fmap (view def_) . resolveWith lookupDef (view tm_)

lookupInContext :: Has (Choose :+: Empty) sig m => QName -> Context -> m (Index, Type)
lookupInContext (QName (m :|> n))
  | m == Nil  = lookupIndex n
  | otherwise = const empty

lookupInTypeContext :: Has (Choose :+: Empty) sig m => QName -> TypeContext.TypeContext -> m (Index, Kind)
lookupInTypeContext (QName (m :|> n))
  | m == Nil  = TypeContext.lookupIndex n
  | otherwise = const empty

-- FIXME: probably we should instead look up the effect op globally, then check for membership in the sig
-- FIXME: return the index in the sig; it’s vital for evaluation of polymorphic effects when there are multiple such
lookupInSig :: Has (Choose :+: Empty) sig m => QName -> Module -> Graph -> [Signature Type] -> m (QName :=: Type)
lookupInSig (QName (m :|> n)) mod graph = foldMapC $ foldMapC (\ (Interface q@(QName (m':|>_)) _) -> do
  guard (m == Nil || m == m')
  defs <- interfaceScope =<< lookupQ graph mod q
  d <- maybe empty pure (defs ^? ix n)
  pure $ QName (m' :|> n) :=: d) . interfaces
  where
  interfaceScope = \case { DSubmodule (SInterface defs) _K -> pure defs ; _ -> empty }


(|-) :: Has (Reader ElabContext) sig m => Name :==> Type -> m a -> m a
p |- b = locally context_ (|> p) b

infixr 1 |-

(||-) :: Has (Reader ElabContext) sig m => Name :==> Kind -> m a -> m a
k ||- b = locally typeContext_ (TypeContext.|> k) b

infix 1 ||-


evalTExpr :: Has (Reader ElabContext :+: State (Subst Type)) sig m => TX.Type -> m Type
evalTExpr texpr = TN.eval <$> get <*> pure Nil <*> pure texpr

depth :: Has (Reader ElabContext) sig m => m Level
depth = views context_ level


-- Errors

pushSpan :: Has (Reader ElabContext) sig m => Span -> m a -> m a
pushSpan = locally spans_ . flip (:>)

withSpanC :: Has (Reader ElabContext) sig m => S.Ann a -> (a -> Type <==: m b) -> Type <==: m b
withSpanC (S.Ann s _ a) k = Check (\ _T -> pushSpan s (k a <==: _T))

withSpan :: Has (Reader ElabContext) sig m => (a -> m b) -> S.Ann a -> m b
withSpan k (S.Ann s _ a) = pushSpan s (k a)



data Err = Err
  { source      :: Source
  , reason      :: ErrReason
  , context     :: Context
  , typeContext :: TypeContext.TypeContext
  , subst       :: Subst Type
  , sig         :: [Signature Type]
  , callStack   :: CallStack
  }

-- FIXME: not all of these need contexts/metacontexts.
data ErrReason
  = FreeVariable QName
  -- FIXME: add source references for the imports, definition sites, and any re-exports.
  | AmbiguousName QName [QName]
  | CouldNotSynthesize
  | UnifyType UnifyErrReason (Exp (Either String Type)) (Act (Either String Type))
  | UnifyKind (Exp (Either String Kind)) (Act Kind)
  | Hole Name Type
  | Invariant String
  | MissingInterface (Interface Type)
  deriving (Show)

_FreeVariable :: Prism' ErrReason QName
_FreeVariable = prism' FreeVariable (\case
  FreeVariable n -> Just n
  _              -> Nothing)

_AmbiguousName :: Prism' ErrReason (QName, [QName])
_AmbiguousName = prism' (uncurry AmbiguousName) (\case
  AmbiguousName n ns -> Just (n, ns)
  _                  -> Nothing)

_UnifyType :: Prism' ErrReason (UnifyErrReason, Exp (Either String Type), Act (Either String Type))
_UnifyType = prism' (\ (r, x, a) -> UnifyType r x a) (\case
  UnifyType r x a -> Just (r, x, a)
  _               -> Nothing)

data UnifyErrReason
  = Mismatch
  | Occurs Meta Type
  deriving (Show)

_Mismatch :: Prism' UnifyErrReason ()
_Mismatch = prism' (const Mismatch) (\case
  Mismatch -> Just ()
  _        -> Nothing)

_Occurs :: Prism' UnifyErrReason (Meta, Type)
_Occurs = prism' (uncurry Occurs) (\case
  Occurs v c -> Just (v, c)
  _          -> Nothing)

applySubst :: Subst Type -> ErrReason -> ErrReason
applySubst subst r = case r of
  FreeVariable{}       -> r
  AmbiguousName{}      -> r
  CouldNotSynthesize{} -> r
  -- NB: not substituting in @r@ because we want to retain the cyclic occurrence (and finitely)
  UnifyType r exp act  -> UnifyType r (fmap roundtrip <$> exp) (fmap roundtrip <$> act)
  UnifyKind{}          -> r
  Hole n t             -> Hole n (roundtrip t)
  Invariant{}          -> r
  MissingInterface i   -> MissingInterface (roundtrip <$> i)
  where
  roundtrip = apply subst Nil


mismatchTypes :: Has (Throw ErrReason) sig m => Exp (Either String Type) -> Act (Either String Type) -> m a
mismatchTypes exp act = withFrozenCallStack $ throwError $ UnifyType Mismatch exp act

mismatchKinds :: Has (Throw ErrReason) sig m => Exp (Either String Kind) -> Act Kind -> m a
mismatchKinds exp act = withFrozenCallStack $ throwError $ UnifyKind exp act

couldNotUnifyKinds :: Has (Throw ErrReason) sig m => Exp Kind -> Act Kind -> m a
couldNotUnifyKinds t1 t2 = withFrozenCallStack $ mismatchKinds (Right <$> t1) t2

couldNotSynthesize :: Has (Throw ErrReason) sig m => m a
couldNotSynthesize = withFrozenCallStack $ throwError CouldNotSynthesize

freeVariable :: Has (Throw ErrReason) sig m => QName -> m a
freeVariable n = withFrozenCallStack $ throwError $ FreeVariable n

-- FIXME: get references for the resolved names
ambiguousName :: Has (Throw ErrReason) sig m => QName -> [QName] -> m a
ambiguousName n ns = withFrozenCallStack $ throwError $ AmbiguousName n ns

missingInterface :: Has (Throw ErrReason) sig m => Interface Type -> m a
missingInterface i = withFrozenCallStack $ throwError $ MissingInterface i


newtype ErrC m a = ErrC { runErr :: m a }
  deriving (Applicative, Functor, Monad)

instance (Has (Reader ElabContext) sig m, Has (Reader Source) sig m, Has (State (Subst Type)) sig m, Has (Throw Err) sig m) => Algebra (Throw ErrReason :+: sig) (ErrC m) where
  alg hdl sig ctx = case sig of
    L (Throw reason) -> do
      source <- ask
      ElabContext{ context, typeContext, sig, spans } <- ask
      subst <- get
      throwError $ Err (maybe source (slice source) (peek spans)) (applySubst subst reason) context typeContext subst sig GHC.Stack.callStack
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
assertTypesMatch pat exp _T = maybe (mismatchTypes (Exp (Left exp)) (Act (Right _T))) pure (_T ^? pat)

assertFunction :: Has (Throw ErrReason) sig m => Type -> m (Maybe Name, Type, Type)
assertFunction = assertTypesMatch _Arrow "_ -> _"


-- Unification

data ElabContext = ElabContext
  { context     :: Context
  , typeContext :: TypeContext.TypeContext
  , sig         :: [Signature Type]
  , spans       :: Snoc Span
  }

context_ :: Lens' ElabContext Context
context_ = lens (\ ElabContext{ context } -> context) (\ ElabContext{ typeContext, sig, spans } context -> ElabContext{ context, typeContext, sig, spans })

typeContext_ :: Lens' ElabContext TypeContext.TypeContext
typeContext_ = lens (\ ElabContext{ typeContext } -> typeContext) (\ ElabContext{ context, sig, spans } typeContext -> ElabContext{ context, typeContext, sig, spans })

sig_ :: Lens' ElabContext [Signature Type]
sig_ = lens (\ ElabContext{ sig } -> sig) (\ ElabContext{ context, typeContext, spans } sig -> ElabContext{ context, typeContext, sig, spans })

spans_ :: Lens' ElabContext (Snoc Span)
spans_ = lens spans (\ e spans -> e{ spans })


-- Machinery

elabWith :: (Subst Type -> a -> m b) -> ReaderC ElabContext (StateC (Subst Type) m) a -> m b
elabWith k = runState k mempty . runReader ElabContext{ context = Context.empty, typeContext = TypeContext.empty, sig = mempty, spans = Nil }

elabKind :: Applicative m => ReaderC ElabContext (StateC (Subst Type) m) Kind -> m Kind
elabKind = elabWith (const pure)

elabType :: (HasCallStack, Applicative m) => ReaderC ElabContext (StateC (Subst Type) m) TX.Type -> m Type
elabType = elabWith (\ subst t -> pure (TN.eval subst Nil t))

elabTerm :: Applicative m => ReaderC ElabContext (StateC (Subst Type) m) Term -> m Term
elabTerm = elabWith (const pure)

elabSynthTerm :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => ReaderC ElabContext (StateC (Subst Type) m) (Term :==> Type) -> m (Term :==> Type)
elabSynthTerm = elabWith (\ subst (e :==> _T) -> pure (e :==> TN.eval subst Nil (runQuoter 0 (quote _T))))

elabSynthType :: (HasCallStack, Has (Reader Graph :+: Reader Module :+: Reader Source) sig m) => ReaderC ElabContext (StateC (Subst Type) m) (TX.Type :==> Kind) -> m (Type :==> Kind)
elabSynthType = elabWith (\ subst (_T :==> _K) -> pure (TN.eval subst Nil _T :==> _K))
