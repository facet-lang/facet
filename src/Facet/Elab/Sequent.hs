{-# LANGUAGE ImplicitParams #-}
module Facet.Elab.Sequent
( -- * Variables
  globalS
, varS
  -- * Constructors
, lamS
, stringS
  -- * Eliminators
, appS
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

import           Control.Effect.Reader
import           Control.Effect.State
import           Control.Effect.Throw
import           Control.Effect.Writer
import           Data.Foldable (fold)
import           Data.Text (Text)
import           Data.Traversable (for)
import           Facet.Context (level)
import           Facet.Effect.Write
import           Facet.Elab
import qualified Facet.Elab.Type as Type
import           Facet.Functor.Check
import           Facet.Functor.Compose
import           Facet.Functor.Synth
import           Facet.Graph
import           Facet.Kind
import           Facet.Lens as Lens (views)
import           Facet.Module
import           Facet.Name
import           Facet.Pattern
import qualified Facet.Pattern.Column as Col
import qualified Facet.Scope as Scope
import           Facet.Semiring
import           Facet.Sequent.Class as SQ
import           Facet.Snoc.NonEmpty
import           Facet.Subst
import qualified Facet.Surface.Term.Expr as S
import qualified Facet.Surface.Type.Expr as S
import           Facet.Syntax as S hiding (context_)
import           Facet.Type.Norm as T
import           Facet.Unify
import           Facet.Usage
import           Fresnel.Getter (view)
import           Fresnel.Lens (Lens, Lens', lens)
import           GHC.Stack (HasCallStack, callStack, popCallStack, withFrozenCallStack)

-- Variables

-- FIXME: we’re instantiating when inspecting types in the REPL.
globalS :: (Has (State (Subst Type)) sig m, SQ.Sequent t c d, Applicative i) => QName ::: Type -> m (i t :==> Type)
globalS (q ::: _T) = do
  v <- SQ.varA (Global q)
  (\ (v ::: _T) -> v :==> _T) <$> instantiate const (v ::: _T)

-- FIXME: do we need to instantiate here to deal with rank-n applications?
-- FIXME: effect ops not in the sig are reported as not in scope
-- FIXME: effect ops in the sig are available whether or not they’re in scope
varS :: (Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m, SQ.Sequent t c d, Applicative i) => QName -> m (i t :==> Type)
varS n = views context_ (lookupInContext n) >>= \case
  [(n', Right (q, _T))] -> do
    use n' q
    d <- views context_ level
    SQ.varA (Free (toLeveled d (ident n'))) ==> pure _T
  _                     -> resolveDef n >>= \case
    DTerm _ _T -> globalS (n ::: _T)
    _          -> freeVariable n

hole :: Has (Throw ErrReason) sig m => Name -> Type <==: m a
hole n = Check $ \ _T -> withFrozenCallStack $ throwError $ Hole n _T


-- Constructors

lamS
  :: (Has (Throw ErrReason) sig m, SQ.Sequent t c d, Applicative i)
  => (forall j . Applicative j => (i ~> j) -> j t :@ Quantity :==> Type -> j c :@ Quantity :==> Type -> Type <==: m (j d))
  -> Type <==: m (i t)
lamS f = runC $ SQ.lamRA $ \ wk a k -> C $ Check $ \ _T -> do
  (_, q, _A, _B) <- assertTacitFunction _T
  check (f wk (a :@ q :==> _A) (k :@ q :==> _B) ::: _B)

stringS :: (Applicative m, SQ.Sequent t c d, Applicative i) => Text -> m (i t :==> Type)
stringS s = SQ.stringRA s ==> pure T.String


-- Eliminators

appS :: (HasCallStack, Has (Reader ElabContext) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m, SQ.Sequent t c d, Applicative i) => (HasCallStack => m (i t :==> Type)) -> (HasCallStack => Type <==: m (i t)) -> m (i t :==> Type)
appS f a = do
  f' :==> _F <- f
  (_, q, _A, _B) <- assertFunction _F
  a' <- censor @Usage (q ><<) $ check (a ::: _A)
  (:==> _B) <$> SQ.µRA (\ wk k -> pure (wk f') SQ..||. SQ.lamLA (pure (wk a')) (pure k))


-- General combinators

switch :: (Has (Reader ElabContext) sig m, Has (Throw ErrReason) sig m, Has (Writer Usage) sig m) => m (a :==> Type) -> Type <==: m a
switch m = Check $ \ _Exp -> do
  a :==> _Act <- m
  a <$ unify (Exp _Exp) (Act _Act)

as :: (Has (Reader ElabContext) sig m, Has (Throw ErrReason) sig m) => (Type <==: m a) ::: m (Type :==> Kind) -> m (a :==> Type)
as (m ::: _T) = do
  _T' <- Type.switch _T <==: KType
  a <- check (m ::: _T')
  pure $ a :==> _T'


-- Elaboration

synthExprS :: (HasCallStack, Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Write Warn) sig m, Has (Writer Usage) sig m, SQ.Sequent t c d, Applicative i) => S.Ann S.Expr -> m (i t :==> Type)
synthExprS = let ?callStack = popCallStack GHC.Stack.callStack in withSpan $ \case
  S.Var n    -> varS n
  S.App f a  -> synthApp f a
  S.As t _T  -> synthAs t _T
  S.String s -> stringS s
  S.Hole{}   -> nope
  S.Lam{}    -> nope
  where
  nope = couldNotSynthesize

synthApp :: (Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Write Warn) sig m, Has (Writer Usage) sig m, SQ.Sequent t c d, Applicative i) => S.Ann S.Expr -> S.Ann S.Expr -> m (i t :==> Type)
synthApp f a = appS (synthExprS f) (checkExprS a)

synthAs :: (HasCallStack, Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Write Warn) sig m, Has (Writer Usage) sig m, SQ.Sequent t c d, Applicative i) => S.Ann S.Expr -> S.Ann S.Type -> m (i t :==> Type)
synthAs t _T = as (checkExprS t ::: do { _T :==> _K <- Type.synthType _T ; (:==> _K) <$> evalTExpr _T })


checkExprS :: (HasCallStack, Has (Reader ElabContext) sig m, Has (Reader Graph) sig m, Has (Reader Module) sig m, Has (State (Subst Type)) sig m, Has (Throw ErrReason) sig m, Has (Write Warn) sig m, Has (Writer Usage) sig m, SQ.Sequent t c d, Applicative i) => S.Ann S.Expr -> Type <==: m (i t)
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
  valPattern (S.PWildcard) = PWildcard
  valPattern (S.PVar n)    = PVar n
  valPattern (S.PCon n fs) = PCon n (map (valPattern . out) fs)

checkLamS
  :: Has (Throw ErrReason) sig m
  => Type <==: [Clause (m (i t))]
  -> Type <==: m (i t)
checkLamS _ = Check (\ _T -> mismatchTypes (Exp (Left "unimplemented")) (Act _T))


data Clause a = Clause
  { patterns :: [Pattern Name]
  , body     :: a
  }
  deriving (Show)

patterns_ :: Lens' (Clause a) [Pattern Name]
patterns_ = lens patterns (\ c patterns -> c{ patterns })

body_ :: Lens (Clause a) (Clause b) a b
body_ = lens body (\ c body -> c{ body })


partitionBy :: [Clause a] -> Scope.Scope Type -> Maybe (Col.Column [Clause a])
partitionBy clauses ctors = fold <$> for clauses (\case
  Clause (PVal p:ps) b -> case p of
    PWildcard       -> pure (Col.fromList ([Clause (PVal PWildcard:ps) b] <$ view Scope.toList_ ctors))
    PVar n          -> pure (Col.fromList ([Clause (PVal (PVar n) :ps) b] <$ view Scope.toList_ ctors))
    PCon (_:|>n) fs -> case Scope.lookupIndex n ctors of
      Nothing -> Nothing
      Just ix -> pure (Col.singleton ix [Clause (map PVal fs <> ps) b])
  _ -> Nothing)


-- Assertions

-- | Expect a tacit (non-variable-binding) function type.
assertTacitFunction :: Has (Throw ErrReason) sig m => Type -> m (Maybe Name, Quantity, Type, Type)
assertTacitFunction = assertTypesMatch _Arrow "_ -> _"


-- Judgements

check :: (Type <==: m a) ::: Type -> m a
check (m ::: _T) = m <==: _T
