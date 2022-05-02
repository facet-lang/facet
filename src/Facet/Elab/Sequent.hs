{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
module Facet.Elab.Sequent
( -- * Variables
  globalS
, varS
  -- * Constructors
, lamS
, lamS'
, stringS
  -- * Eliminators
, appS
  -- * General combinators
, freshName
  -- * Elaboration
, synthExprS
, checkExprS
, Clause(..)
, patterns_
, body_
, partitionBy
  -- * Assertions
, assertTacitFunction
  -- * Judgements
, check
) where

import           Control.Effect.Empty
import           Control.Effect.Fresh
import           Control.Effect.Reader
import           Control.Effect.State
import           Control.Effect.Throw
import           Data.Foldable (fold)
import           Data.Text (Text)
import           Data.Traversable (for)
import           Facet.Effect.Write
import           Facet.Elab
import qualified Facet.Elab.Type as Type
import           Facet.Functor.Check
import           Facet.Functor.Synth
import           Facet.Graph
import           Facet.Kind
import           Facet.Lens as Lens (views)
import           Facet.Module
import           Facet.Name
import           Facet.Pattern
import qualified Facet.Pattern.Column as Col
import qualified Facet.Scope as Scope
import           Facet.Sequent.Expr as SQ
import           Facet.Snoc.NonEmpty
import           Facet.Subst
import qualified Facet.Surface.Term.Expr as S
import qualified Facet.Surface.Type.Expr as S
import           Facet.Syntax as S hiding (context_)
import           Facet.Type.Norm as T
import           Facet.Unify
import           Fresnel.Getter (view)
import           Fresnel.Lens (Lens, Lens', lens)
import           GHC.Stack (HasCallStack, callStack, popCallStack, withFrozenCallStack)

-- Variables

-- FIXME: we’re instantiating when inspecting types in the REPL.
globalS :: Has (State (Subst Type)) sig m => QName ::: Type -> m (SQ.Term :==> Type)
globalS (q ::: _T) = do
  let v = SQ.Var (Free q)
  (\ (v ::: _T) -> v :==> _T) <$> instantiate const (v ::: _T)

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
varS :: (Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m) => QName -> m (SQ.Term :==> Type)
varS n = views context_ (lookupInContext n) >>= \case
  [(i, _T)] -> pure $ SQ.Var (Bound i) :==> _T
  _         -> resolveDef n >>= \case
    DTerm _ _T -> globalS (n ::: _T)
    _          -> freeVariable n

hole :: Has (Throw ErrReason) sig m => Name -> Type <==: m a
hole n = Check $ \ _T -> withFrozenCallStack $ throwError $ Hole n _T


-- Constructors

lamS
  :: (Has Fresh sig m, Has (Throw ErrReason) sig m)
  => (Type <==: m SQ.Term -> Type <==: m SQ.Coterm -> Type <==: m SQ.Command)
  -> Type <==: m SQ.Term
lamS b = Check $ \ _T -> do
  (_, _A, _B) <- assertTacitFunction _T
  v <- freshName "v"
  k <- freshName "k"
  SQ.lamR v k <$> check (b (pure (pure (SQ.localR v))) (pure (pure (SQ.localL k))) ::: _B)

lamS'
  :: (Has Fresh sig m, Has (Throw ErrReason) sig m)
  => (Type <==: m SQ.Term -> Type <==: m SQ.Term)
  -> Type <==: m SQ.Term
lamS' b = lamS (\ v k -> b v >< k)

stringS :: Applicative m => Text -> m (SQ.Term :==> Type)
stringS s = pure $ SQ.StringR s :==> T.String


-- Eliminators

appS :: (HasCallStack, Has Fresh sig m, Has (Throw ErrReason) sig m) => (HasCallStack => m (SQ.Term :==> Type)) -> (HasCallStack => Type <==: m SQ.Term) -> m (SQ.Term :==> Type)
appS f a = do
  f' :==> _F <- f
  (_, _A, _B) <- assertFunction _F
  a' <- check (a ::: _A)
  k <- freshName "k"
  pure $ SQ.muR k (f' SQ.:|: SQ.LamL a' (SQ.Covar (Free (q k)))) :==> _B


-- General combinators

switch :: (Has (Reader ElabContext) sig m, Has (Throw ErrReason) sig m) => m (a :==> Type) -> Type <==: m a
switch m = Check $ \ _Exp -> do
  a :==> _Act <- m
  a <$ unify (Exp _Exp) (Act _Act)

as :: (Has (Reader ElabContext) sig m, Has (Throw ErrReason) sig m) => (Type <==: m a) ::: m (Type :==> Kind) -> m (a :==> Type)
as (m ::: _T) = do
  _T' <- Type.switch _T <==: KType
  a <- check (m ::: _T')
  pure $ a :==> _T'

freshName :: Has Fresh sig m => Text -> m Name
freshName s = G s <$> fresh


-- Elaboration

synthExprS :: (HasCallStack, Has Fresh sig m, Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Write Warn) sig m) => S.Ann S.Expr -> m (SQ.Term :==> Type)
synthExprS = let ?callStack = popCallStack GHC.Stack.callStack in withSpan $ \case
  S.Var n    -> varS n
  S.App f a  -> synthApp f a
  S.As t _T  -> synthAs t _T
  S.String s -> stringS s
  S.Hole{}   -> nope
  S.Lam{}    -> nope
  where
  nope = couldNotSynthesize

synthApp :: (Has Fresh sig m, Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Write Warn) sig m) => S.Ann S.Expr -> S.Ann S.Expr -> m (SQ.Term :==> Type)
synthApp f a = appS (synthExprS f) (checkExprS a)

synthAs :: (HasCallStack, Has Fresh sig m, Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Write Warn) sig m) => S.Ann S.Expr -> S.Ann S.Type -> m (SQ.Term :==> Type)
synthAs t _T = as (checkExprS t ::: do { _T :==> _K <- Type.synthType _T ; (:==> _K) <$> evalTExpr _T })


checkExprS :: (HasCallStack, Has Fresh sig m, Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Write Warn) sig m) => S.Ann S.Expr -> Type <==: m SQ.Term
checkExprS expr = let ?callStack = popCallStack GHC.Stack.callStack in withSpanC expr $ \case
  S.Hole n   -> hole n
  S.Lam cs   -> checkLamS (Check (\ _T -> map (\ (S.Clause (S.Ann _ _ p) b) -> Clause [pattern p] (check (checkExprS b ::: _T))) cs))
  S.Var{}    -> switch (synthExprS expr)
  S.App{}    -> switch (synthExprS expr)
  S.As{}     -> switch (synthExprS expr)
  S.String{} -> switch (synthExprS expr)
  where
  pattern (S.PVal (Ann _ _ p))                        = PVal (valPattern p)
  pattern (S.PEff (Ann _ _ (S.POp n fs (Ann _ _ k)))) = PEff (POp n (map (valPattern . out) fs) (valPattern k))
  valPattern S.PWildcard   = PWildcard
  valPattern (S.PVar n)    = PVar n
  valPattern (S.PCon n fs) = PCon n (map (valPattern . out) fs)

checkLamS
  :: Has (Throw ErrReason) sig m
  => Type <==: [Clause (m SQ.Term)]
  -> Type <==: m SQ.Term
checkLamS _ = Check (mismatchTypes (Exp (Left "unimplemented")) . Act)


data Clause a = Clause
  { patterns :: [Pattern Name]
  , body     :: a
  }
  deriving (Show)

patterns_ :: Lens' (Clause a) [Pattern Name]
patterns_ = lens patterns (\ c patterns -> c{ patterns })

body_ :: Lens (Clause a) (Clause b) a b
body_ = lens body (\ c body -> c{ body })


partitionBy :: Has Empty sig m => [Clause a] -> Scope.Scope Type -> m (Col.Column [Clause a])
partitionBy clauses ctors = fold <$> for clauses (\case
  Clause (PVal p:ps) b -> case p of
    PWildcard       -> pure (Col.fromList ([Clause (PVal PWildcard:ps) b] <$ view Scope.toList_ ctors))
    PVar n          -> pure (Col.fromList ([Clause (PVal (PVar n) :ps) b] <$ view Scope.toList_ ctors))
    PCon (_:|>n) fs -> case Scope.lookupIndex n ctors of
      Nothing -> empty
      Just ix -> pure (Col.singleton ix [Clause (map PVal fs <> ps) b])
  _ -> empty)


-- Assertions

-- | Expect a tacit (non-variable-binding) function type.
assertTacitFunction :: Has (Throw ErrReason) sig m => Type -> m (Maybe Name, Type, Type)
assertTacitFunction = assertTypesMatch _Arrow "_ -> _" -- FIXME: this binds non-tacit functions


-- Judgements

check :: (Type <==: m a) ::: Type -> m a
check (m ::: _T) = m <==: _T
