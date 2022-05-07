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
, patternBody
-- , partitionBy
  -- * Assertions
, assertTacitFunction
  -- * Judgements
, check
) where

import           Control.Applicative (liftA2)
import           Control.Effect.Empty
import           Control.Effect.Fresh
import           Control.Effect.Reader
import           Control.Effect.State
import           Control.Effect.Throw
import           Data.Maybe (fromMaybe, mapMaybe)
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
import qualified Facet.Scope as Scope
import qualified Facet.Sequent.Expr as SQ
import           Facet.Subst
import qualified Facet.Surface.Term.Expr as S
import qualified Facet.Surface.Type.Expr as S
import           Facet.Syntax as S hiding (context_)
import           Facet.Type.Norm as T hiding (($$))
import           Facet.Unify
import           Fresnel.Fold ((^?))
import           Fresnel.Lens (Lens, Lens', lens)
import           GHC.Stack (HasCallStack, callStack, popCallStack, withFrozenCallStack)

-- Variables

-- FIXME: we’re instantiating when inspecting types in the REPL.
globalS :: Has (State (Subst Type)) sig m => QName ::: Type -> m (SQ.Term :==> Type)
globalS (q ::: _T) = do
  let v = SQ.globalR q
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
  SQ.lamR v k <$> check (b (pure (pure (SQ.localR v))) (localL k) ::: _B)

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
  S.Lam cs   -> checkLamS (map (\ (S.Clause (S.Ann _ _ p) b) -> Clause [pattern p] (checkExprS b)) cs)
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
  :: (Has Fresh sig m, Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m)
  => [Clause (Type <==: m SQ.Term)]
  -> Type <==: m SQ.Term
checkLamS clauses = Check (go id)
  where
  go scrutinees = \case
    T.Arrow _ _A _B -> do
      x <- freshName "x"
      SQ.lamR' x <$> go (scrutinees . ((x :==> _A) :)) _B
    _T              -> do
      x <- freshName "x"
      kx <- freshName "kx"
      SQ.lamR x kx <$> check (patternBody (scrutinees []) (map (fmap (>< localL kx)) clauses) ::: _T)


data Clause a = Clause
  { patterns :: [Pattern Name]
  , body     :: a
  }
  deriving (Functor, Show)

patterns_ :: Lens' (Clause a) [Pattern Name]
patterns_ = lens patterns (\ c patterns -> c{ patterns })

body_ :: Lens (Clause a) (Clause b) a b
body_ = lens body (\ c body -> c{ body })


-- FIXME: try returning a coterm instead of a command
patternBody
  :: (Has Fresh sig m, Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (Throw ErrReason) sig m)
  => [Name :==> Type]
  -> [Clause (Type <==: m SQ.Command)]
  -> Type <==: m SQ.Command
patternBody scrutinees clauses = Check $ \ _T -> case scrutinees of
  (s :==> _A):scrutinees' -> case _A of
    Ne (Free qname) _ -> do
      def <- resolveDef qname
      let constructors = fromMaybe [] (def ^? (_DData . Scope.toList_)) -- FIXME: throw an error if we can't find the datatype

          filterClauses name fieldTypes c = case c of
            Clause (PVal PWildcard  :ps) b -> Just (Clause (padding <> ps) b)
            Clause (PVal (PVar n)   :ps) b -> Just (Clause (padding <> ps) (fmap (n :==> _A |-) b))
            Clause (PVal (PCon n fs):ps) b
              | n == q name -> Just (Clause (map PVal fs <> ps) b)
            _                              -> Nothing
            where
            padding = replicate (length fieldTypes) (PVal PWildcard)

      groups <- for constructors (\ (name :=: _C) -> do
        let fieldTypes = argumentTypes _C
        prefix <- for fieldTypes (\ _T -> (:==> _T) <$> freshName "x")
        pure (name :=: muL (const (patternBody (prefix <> scrutinees') (mapMaybe (filterClauses name fieldTypes) clauses)))))

      check (localR s >< case' groups ::: _T)

    -- FIXME: what should effect patterns elaborate to?
    _                 -> check (patternBody scrutinees' (clauses >>= \case
      Clause (PVal PWildcard:ps) b -> [Clause ps b]
      Clause (PVal (PVar n) :ps) b -> [Clause ps (fmap (n :==> _A |-) b)]
      Clause _ _                   -> []) ::: _T)

  [] -> check (body (head clauses) ::: _T) -- FIXME: throw an error if there aren't any clauses left


localL :: Applicative m => Name -> Type <==: m SQ.Coterm
localL = pure . pure . SQ.localL

muL :: (Has Fresh sig m, Has (Reader ElabContext) sig m) => (SQ.Term -> Type <==: m SQ.Command) -> Type <==: m SQ.Coterm
muL body = Check $ \ _T -> do
  x <- freshName "x"
  SQ.muL x <$> (x :==> _T |- check (body (SQ.localR x) ::: _T))

localR :: Applicative m => Name -> Type <==: m SQ.Term
localR = pure . pure . SQ.localR

(><) :: Applicative m => Type <==: m SQ.Term -> Type <==: m SQ.Coterm -> Type <==: m SQ.Command
t >< c = Check $ \ _T -> liftA2 (SQ.:|:) (check (t ::: _T)) (check (c ::: _T))

infix 3 ><

case' :: Has Fresh sig m => [Name :=: (Type <==: m SQ.Coterm)] -> Type <==: m SQ.Coterm
case' cases = Check $ \ _T -> SQ.SumL <$> traverse (traverse (\ body -> check (body ::: _T))) cases


argumentTypes :: Type -> [Type]
argumentTypes (T.Arrow _ _A _B) = _A : argumentTypes _B
argumentTypes _                 = []


-- Assertions

-- | Expect a tacit (non-variable-binding) function type.
assertTacitFunction :: Has (Throw ErrReason) sig m => Type -> m (Maybe Name, Type, Type)
assertTacitFunction = assertTypesMatch _Arrow "_ -> _" -- FIXME: this binds non-tacit functions


-- Judgements

check :: (Type <==: m a) ::: Type -> m a
check (m ::: _T) = m <==: _T
