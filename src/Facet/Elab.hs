{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Elab
( M(..)
, Val
, Type
, Expr
, Elab(..)
, Check(..)
, Synth(..)
, check
, unify
  -- * General
, global
  -- * Types
, elabType
, _Type
, _Unit
, (.*)
, (-->)
, (>~>)
  -- * Expressions
, elabExpr
, ($$)
, tlam
, lam
, unit
, (**)
  -- * Declarations
, elabDecl
  -- * Modules
, elabModule
  -- * Errors
, ErrDoc
, Err(..)
, Reason(..)
) where

import           Control.Algebra
import           Control.Applicative (liftA2)
import           Control.Carrier.Error.Church
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Effect.Parser.Span (Span(..))
import           Control.Effect.Sum
import           Data.Bifunctor (first)
import           Data.Foldable (foldl', toList)
import qualified Data.IntMap as IntMap
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Text as T
import           Data.Traversable (for)
import           Facet.Context
import qualified Facet.Core.Module as CM
import qualified Facet.Core.Pattern as CP
import           Facet.Core.Value hiding (bound, global, ($$))
import qualified Facet.Core.Value as CV
import qualified Facet.Env as Env
import           Facet.Name (DName, Index(..), Level(..), QName(..), UName, __)
import           Facet.Stack hiding ((!?))
import qualified Facet.Surface.Decl as SD
import qualified Facet.Surface.Expr as SE
import qualified Facet.Surface.Module as SM
import qualified Facet.Surface.Pattern as SP
import qualified Facet.Surface.Type as ST
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding ((**))
import           Prettyprinter (Doc)
import           Prettyprinter.Render.Terminal (AnsiStyle)
import           Text.Parser.Position (Spanned)

type Val = Value
type Type = Value
type Expr = Value
type Prob = Value

newtype M v a = M { rethrow :: forall sig m . Has (State (Subst v) :+: Throw (Err v)) sig m => m a }

instance Functor (M v) where
  fmap f (M m) = M (fmap f m)

instance Applicative (M v) where
  pure a = M $ pure a
  M f <*> M a = M (f <*> a)

instance Monad (M v) where
  M m >>= f = M $ m >>= rethrow . f

instance Algebra (State (Subst v) :+: Throw (Err v)) (M v) where
  alg hdl sig ctx = case sig of
    L smctx -> M $ alg (rethrow . hdl) (inj smctx) ctx
    R throw -> M $ alg (rethrow . hdl) (inj throw) ctx


newtype Elab v a = Elab { elab :: forall sig m . Has (Reader (Env.Env (Type v)) :+: Reader (Context (Val v ::: Type v)) :+: Reader Span :+: Throw (Err v)) sig m => m a }

instance Functor (Elab v) where
  fmap f (Elab m) = Elab (fmap f m)

instance Applicative (Elab v) where
  pure a = Elab $ pure a
  Elab f <*> Elab a = Elab (f <*> a)

instance Monad (Elab v) where
  Elab m >>= f = Elab $ m >>= elab . f

instance Algebra (Reader (Env.Env (Type v)) :+: Reader (Context (Val v ::: Type v)) :+: Reader Span :+: Throw (Err v)) (Elab v) where
  alg hdl sig ctx = case sig of
    L renv          -> Elab $ alg (elab . hdl) (inj renv) ctx
    R (L rctx)      -> Elab $ alg (elab . hdl) (inj rctx) ctx
    R (R (L rspan)) -> Elab $ alg (elab . hdl) (inj rspan) ctx
    R (R (R throw)) -> Elab $ alg (elab . hdl) (inj throw) ctx


type Subst v = IntMap.IntMap (Maybe (Prob v) ::: Type v)

newtype Unify v a = Unify { runUnify :: forall sig m . Has (Reader (Env.Env (Type v)) :+: Reader (Context (Val v ::: Type v)) :+: Reader Span :+: State (Subst v) :+: Throw (Err v)) sig m => m a }

instance Functor (Unify v) where
  fmap f (Unify m) = Unify (fmap f m)

instance Applicative (Unify v) where
  pure a = Unify $ pure a
  Unify f <*> Unify a = Unify (f <*> a)

instance Monad (Unify v) where
  Unify m >>= f = Unify $ m >>= runUnify . f

instance Algebra (Reader (Env.Env (Type v)) :+: Reader (Context (Val v ::: Type v)) :+: Reader Span :+: State (Subst v) :+: Throw (Err v)) (Unify v) where
  alg hdl sig ctx = case sig of
    L renv              -> Unify $ alg (runUnify . hdl) (inj renv) ctx
    R (L rctx)          -> Unify $ alg (runUnify . hdl) (inj rctx) ctx
    R (R (L rspan))     -> Unify $ alg (runUnify . hdl) (inj rspan) ctx
    R (R (R (L smctx))) -> Unify $ alg (runUnify . hdl) (inj smctx) ctx
    R (R (R (R throw))) -> Unify $ alg (runUnify . hdl) (inj throw) ctx


askEnv :: Has (Reader (Env.Env (Type v))) sig (t v) => t v (Env.Env (Type v))
askEnv = ask

askContext :: Has (Reader (Context (Val v ::: Type v))) sig (t v) => t v (Context (Val v ::: Type v))
askContext = ask


newtype Check v a = Check { runCheck :: Type v -> Elab v a }
  deriving (Algebra (Reader (Type v) :+: Reader (Env.Env (Type v)) :+: Reader (Context (Val v ::: Type v)) :+: Reader Span :+: Throw (Err v)), Applicative, Functor, Monad) via ReaderC (Type v) (Elab v)

newtype Synth v a = Synth { synth :: Elab v (a ::: Type v) }

instance Functor (Synth v) where
  fmap f (Synth m) = Synth (first f <$> m)

check :: (Check v a ::: Type v) -> Elab v a
check = uncurryAnn runCheck


checkElab :: (Maybe (Type v) -> Elab v (a ::: Type v)) -> Check v a
checkElab f = tm <$> Check (f . Just)

synthElab :: (Maybe (Type v) -> Elab v (a ::: Type v)) -> Synth v a
synthElab f = Synth (f Nothing)


unify
  :: forall v
  .  Eq v
  => Type v :===: Type v
  -> Elab v (Type v)
unify (t1 :===: t2) = evalState (IntMap.empty @(Maybe (Prob v) ::: Type v)) . runUnify $ go (t1 :===: t2)
  where
  go
    :: Prob v :===: Prob v
    -> Unify v (Type v)
  go = \case
    -- FIXME: this is missing a lot of cases
    Type       :===: Type       -> pure Type
    Void       :===: Void       -> pure Void
    TUnit      :===: TUnit      -> pure TUnit
    Unit       :===: Unit       -> pure Unit
    -- FIXME: resolve globals to try to progress past certain inequalities
    Neut h1 e1 :===: Neut h2 e2
      | h1 == h2
      , Just e' <- unifyS (e1 :===: e2) -> Neut h1 <$> e'
    Neut (Metavar v) Nil :===: x -> solve (v := x)
    x :===: Neut (Metavar v) Nil -> solve (v := x)
    a1 :-> b1  :===: a2 :-> b2  -> (:->) <$> go (a1 :===: a2) <*> go (b1 :===: b2)
    t1 :=> b1  :===: t2 :=> b2  -> do
      t <- go (ty t1 :===: ty t2)
      b <- tm t1 ::: t |- \ v -> do
        let b1' = b1 v
            b2' = b2 v
        go (b1' :===: b2')
      pure $ tm t1 ::: t :=> b
    t :=> b :===: x -> do
      -- FIXME: how do we eliminate type lambdas in the value? we don’t _have_ the value here, so we can’t apply the meta.
      let _T = ty t
      v <- meta _T
      let _B' = b v
      go (_B' :===: x)
    TPrd l1 r1 :===: TPrd l2 r2 -> TPrd <$> go (l1 :===: l2) <*> go (r1 :===: r2)
    Prd  l1 r1 :===: Prd  l2 r2 -> Prd  <$> go (l1 :===: l2) <*> go (r1 :===: r2)
    -- FIXME: build and display a diff of the root types
    t1 :===: t2                 -> couldNotUnify t1 t2

  unifyS (Nil          :===: Nil)          = Just (pure Nil)
  -- NB: we make no attempt to unify case eliminations because they shouldn’t appear in types anyway.
  unifyS (i1 :> App l1 :===: i2 :> App l2) = liftA2 (:>) <$> unifyS (i1 :===: i2) <*> Just (App <$> go (l1 :===: l2))
  unifyS _                                 = Nothing

  solve :: Level := Prob v -> Unify v (Val v)
  solve (n := val') = do
    subst <- getSubst
    -- FIXME: occurs check
    case subst IntMap.! getLevel n of
      Just val ::: _T -> go (val :===: val')
      Nothing  ::: _T -> val' <$ put (insertSubst n (Just val' ::: _T) subst)


meta :: Type v -> Unify v (Prob v)
meta _T = do
  subst <- getSubst
  let m = Level (length subst)
  put (insertSubst m (Nothing ::: _T) subst)
  pure $ CV.metavar m

insertSubst :: Level -> Maybe (Prob v) ::: Type v -> Subst v -> Subst v
insertSubst n (v ::: _T) = IntMap.insert (getLevel n) (v ::: _T)

getSubst :: Has (State (Subst v)) sig (t v) => t v (Subst v)
getSubst = get



-- General

switch
  :: Eq v
  => Synth v (Val v)
  -> Maybe (Type v)
  -> Elab v (Val v ::: Type v)
switch (Synth m) = \case
  Just _K -> m >>= \ (a ::: _K') -> (a :::) <$> unify (_K' :===: _K)
  _       -> m

global
  :: DName
  -> Synth v (Val v)
global n = Synth $ Env.lookup n <$> askEnv >>= \case
  Just b  -> pure (CV.global (tm b :.: n) ::: ty b)
  Nothing -> freeVariable n

bound
  :: Index
  -> Synth v (Val v)
bound n = Synth $ do
  ctx <- askContext
  -- FIXME: this assumes that the core & surface languages have identical binding structure, which in general they do not.
  case ctx !? n of
    Just (_ ::: (v ::: _T)) -> pure (v ::: _T)
    Nothing                 -> err $ BadContext n

hole
  :: T.Text
  -> Check v a
hole n = Check $ \ _T -> err $ Hole n _T

($$)
  :: Synth v (Val v)
  -> Check v (Val v)
  -> Synth v (Val v)
f $$ a = Synth $ do
  f' ::: _F <- synth f
  (_A, _B) <- expectFunctionType "in application" _F
  a' <- check (a ::: _A)
  pure $ (f' CV.$$ a') ::: _B


(|-)
  :: Has (Reader (Context (Val v ::: Type v))) sig (t v)
  => UName ::: Type v
  -> (Val v -> t v (Val v))
  -> t v (Val v -> Val v)
n ::: _T |- f = do
  ctx <- askContext
  handleBinder (level ctx) (\ v -> local (|> (n ::: v ::: _T)) (f v))

infix 1 |-

(|-*)
  :: Has (Reader (Context (Val v ::: Type v))) sig (t v)
  => CP.Pattern (UName ::: Type v)
  -> (CP.Pattern (Val v) -> t v (Val v))
  -> t v (CP.Pattern (Val v) -> Val v)
p |-* f = do
  ctx <- askContext
  handleBinderP (level ctx) p (\ v ->
    local (flip (foldl' (|>)) (zipWith (\ (n ::: _T) v -> n ::: v ::: _T) (toList p) (toList v))) (f v))

infix 1 |-*


-- Types

elabType
  :: (HasCallStack, Eq v)
  => Context (Type v)
  -> Spanned (ST.Type Spanned a)
  -> Maybe (Type v)
  -> Elab v (Type v ::: Type v)
elabType ctx = withSpan' $ \case
  ST.Free  n -> switch $ global n
  ST.Bound n -> switch $ bound n
  ST.Hole  n -> check (hole n) "hole"
  ST.Type    -> switch $ _Type
  ST.Void    -> switch $ _Void
  ST.Unit    -> switch $ _Unit
  t ST.:=> b -> switch $ fmap (checkElab . elabType ctx) t >~> checkElab (elabType ctx b)
  f ST.:$  a -> switch $ synthElab (elabType ctx f) $$  checkElab (elabType ctx a)
  a ST.:-> b -> switch $ checkElab (elabType ctx a) --> checkElab (elabType ctx b)
  l ST.:*  r -> switch $ checkElab (elabType ctx l) .*  checkElab (elabType ctx r)
  where
  check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T


_Type :: Synth v (Type v)
_Type = Synth $ pure $ Type ::: Type

_Void :: Synth v (Type v)
_Void = Synth $ pure $ Void ::: Type

_Unit :: Synth v (Type v)
_Unit = Synth $ pure $ Unit ::: Type

(.*)
  :: Check v (Type v)
  -> Check v (Type v)
  -> Synth v (Type v)
a .* b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ (TPrd a' b') ::: Type

infixl 7 .*

(-->)
  :: Check v (Type v)
  -> Check v (Type v)
  -> Synth v (Type v)
a --> b = Synth $ do
  a' <- check (a ::: Type)
  b' <- check (b ::: Type)
  pure $ (a' :-> b') ::: Type

infixr 2 -->

(>~>)
  :: (UName ::: Check v (Type v))
  -> Check v (Type v)
  -> Synth v (Type v)
(n ::: t) >~> b = Synth $ do
  _T <- check (t ::: Type)
  -- FIXME: shouldn’t we use the bound variable?
  b' <- n ::: _T |- \ v -> check (b ::: Type)
  pure $ (n ::: _T :=> b') ::: Type

infixr 1 >~>


-- Expressions

elabExpr
  :: (HasCallStack, Eq v)
  => Spanned (SE.Expr Spanned a)
  -> Maybe (Type v)
  -> Elab v (Expr v ::: Type v)
elabExpr = withSpan' $ \case
  SE.Free  n -> switch $ global n
  SE.Bound n -> switch $ bound n
  SE.Hole  n -> check (hole n) "hole"
  f SE.:$  a -> switch $ synthElab (elabExpr f) $$ checkElab (elabExpr a)
  l SE.:*  r -> check (checkElab (elabExpr l) ** checkElab (elabExpr r)) "product"
  SE.Unit    -> switch unit
  SE.Comp cs -> check (elabComp cs) "computation"
  where
  check m msg _T = expectChecked _T msg >>= \ _T -> (::: _T) <$> runCheck m _T


tlam
  :: UName
  -> Check v (Expr v)
  -> Check v (Expr v)
tlam n b = Check $ \ ty -> do
  (_ ::: _T, _B) <- expectQuantifiedType "when checking type lambda" ty
  b' <- n ::: _T |- \ v -> do
    let _B' = _B v
    check (b ::: _B')
  pure (Lam n b')

lam
  :: UName
  -> Check v (Expr v)
  -> Check v (Expr v)
lam n b = Check $ \ _T -> do
  (_A, _B) <- expectFunctionType "when checking lambda" _T
  -- FIXME: shouldn’t we use the bound variable?
  b' <- (n ::: _A) |- \ v -> check (b ::: _B)
  pure (Lam n b')

unit :: Synth v (Expr v)
unit = Synth . pure $ Unit ::: TUnit

(**)
  :: Check v (Expr v)
  -> Check v (Expr v)
  -> Check v (Expr v)
l ** r = Check $ \ _T -> do
  (_L, _R) <- expectProductType "when checking product" _T
  l' <- check (l ::: _L)
  r' <- check (r ::: _R)
  pure (Prd l' r')

elabComp
  :: (HasCallStack, Eq v)
  => Spanned (SE.Comp Spanned a)
  -> Check v (Expr v)
elabComp = withSpan $ \case
  SE.Expr    b  -> checkElab (elabExpr b)
  SE.Clauses cs -> elabClauses cs

data XOr a b
  = XB
  | XL a
  | XR b
  | XT

instance (Semigroup a, Semigroup b) => Semigroup (XOr a b) where
  XB   <> b    = b
  a    <> XB   = a
  XL a <> XL b = XL (a <> b)
  XR a <> XR b = XR (a <> b)
  _    <> _    = XT

instance (Semigroup a, Semigroup b) => Monoid (XOr a b) where
  mempty = XB

elabClauses :: Eq v => [(NonEmpty (Spanned (SP.Pattern Spanned UName)), Spanned (SE.Expr Spanned a))] -> Check v (Expr v)
elabClauses cs = Check $ \ _T -> do
  (_A, _B) <- expectFunctionType "when checking clauses" _T
  rest <- case foldMap partitionClause cs of
    XB    -> pure $ Nothing
    XL _  -> pure $ Nothing
    XR cs -> pure $ Just cs
    XT    -> error "mixed" -- FIXME: throw a proper error
  cs' <- for cs $ \ (p:|_, b) -> do
    p' <- check (elabPattern p ::: _A)
    -- FIXME: shouldn’t this be doing smething with the variable? I mean come on
    b' <- p' |-* \ v -> check (maybe (checkElab (elabExpr b)) elabClauses rest ::: _B)
    pure (tm <$> p', b')
  b' <- __ ::: _A |- \ v -> pure (case' v cs')
  pure $ Lam __ b'
  where
  partitionClause (_:|ps, b) = case ps of
    []   -> XL ()
    p:ps -> XR [(p:|ps, b)]


elabPattern
  :: Eq v
  => Spanned (SP.Pattern Spanned UName)
  -> Check v (CP.Pattern (UName ::: Type v))
elabPattern = withSpan $ \case
  SP.Wildcard -> pure CP.Wildcard
  SP.Var n    -> Check $ \ _T -> pure (CP.Var (n ::: _T))
  SP.Tuple ps -> Check $ \ _T -> CP.Tuple . toList <$> go _T (fromList ps)
    where
    go _T = \case
      Nil      -> case _T of
        TUnit -> pure Nil
        _     -> mismatch "when checking empty tuple pattern" (Right TUnit) _T
      Nil :> p -> (Nil :>) <$> check (elabPattern p ::: _T)
      ps  :> p -> do
        (_L, _R) <- expectProductType "when checking tuple pattern" _T
        (:>) <$> go _L ps <*> check (elabPattern p ::: _R)


-- Declarations

elabDecl
  :: (HasCallStack, Eq v)
  => Context (Type v)
  -> Spanned (SD.Decl Spanned a)
  -> Check v (Expr v) ::: Check v (Type v)
elabDecl ctx = withSpans $ \case
  (n ::: t) SD.:=> b ->
    let b' ::: _B = elabDecl ctx b
    in tlam n b' ::: checkElab (switch (n ::: checkElab (elabType ctx t) >~> _B))

  (n ::: t) SD.:-> b ->
    let b' ::: _B = elabDecl ctx b
    -- FIXME: types and terms are bound with the same context, so the indices in the type are incremented, but arrow types don’t extend the context, so we were mishandling them.
    in lam n b' ::: checkElab (switch (checkElab (elabType ctx t) --> local (|> (n ::: (Type `asParameterOf` b') ::: (Type `asParameterOf` b'))) _B))

  t SD.:= b ->
    checkElab (elabExpr b) ::: checkElab (elabType empty t)
  where
  withSpans f (s, d) = let t ::: _T = f d in setSpan s t ::: setSpan s _T

  asParameterOf :: a -> f a -> a
  asParameterOf = const


-- Modules

elabModule
  :: forall v a m sig
  .  (HasCallStack, Has (Throw (Err v)) sig m, Eq v)
  => Spanned (SM.Module Spanned a)
  -> m (CM.Module v)
elabModule (s, SM.Module mname ds) = runReader s . evalState (mempty @(Env.Env (Type v))) $ do
  -- FIXME: elaborate all the types first, and only then the terms
  -- FIXME: maybe figure out the graph for mutual recursion?
  defs <- for ds $ \ (s, (n, d)) -> setSpan s $ do
    env <- get @(Env.Env (Type v))
    e' ::: _T <- runReader @(Context (Val v ::: Type v)) empty . runReader env $ do
      let e ::: t = elabDecl empty d
      _T <- elab $ check (t ::: Type)
      e' <- elab $ check (e ::: _T)
      pure $ e' ::: _T

    modify $ Env.insert (mname :.: n ::: _T)
    -- FIXME: extend the module
    -- FIXME: support defining types
    pure (mname :.: n, CM.DTerm e' ::: _T)

  pure $ CM.Module mname defs


-- Errors

setSpan :: Has (Reader Span) sig m => Span -> m a -> m a
setSpan = local . const

withSpan :: Has (Reader Span) sig m => (a -> m b) -> (Span, a) -> m b
withSpan k (s, a) = setSpan s (k a)

withSpan' :: Has (Reader Span) sig m => (a -> b -> m c) -> (Span, a) -> b -> m c
withSpan' k (s, a) b = setSpan s (k a b)


type ErrDoc = Doc AnsiStyle

data Err v = Err
  { span    :: Span
  , reason  :: Reason v
  , context :: Context (Val v ::: Type v)
  }

data Reason v
  = FreeVariable DName
  | CouldNotSynthesize String
  | Mismatch String (Either String (Type v)) (Type v)
  | Hole T.Text (Type v)
  | BadContext Index


err :: Has (Reader (Context (Val v ::: Type v)) :+: Reader Span :+: Throw (Err v)) sig (t v) => Reason v -> t v a
err reason = do
  span <- ask
  ctx <- askContext
  throwError $ Err span reason ctx

mismatch :: Has (Reader (Context (Val v ::: Type v)) :+: Reader Span :+: Throw (Err v)) sig (t v) => String -> Either String (Type v) -> Type v -> t v a
mismatch msg exp act = err $ Mismatch msg exp act

couldNotUnify :: Has (Reader (Context (Val v ::: Type v)) :+: Reader Span :+: Throw (Err v)) sig (t v) => Type v -> Type v -> t v a
couldNotUnify t1 t2 = mismatch "mismatch" (Right t2) t1

couldNotSynthesize :: String -> Elab v a
couldNotSynthesize = err . CouldNotSynthesize

freeVariable :: DName -> Elab v a
freeVariable = err . FreeVariable

expectChecked :: Maybe (Type v) -> String -> Elab v (Type v)
expectChecked t msg = maybe (couldNotSynthesize msg) pure t


-- Patterns

expectMatch :: (Type v -> Maybe out) -> String -> String -> Type v -> Elab v out
expectMatch pat exp s _T = maybe (mismatch s (Left exp) _T) pure (pat _T)

expectQuantifiedType :: String -> Type v -> Elab v (UName ::: Type v, Type v -> Type v)
expectQuantifiedType = expectMatch unForAll "{_} -> _"

expectFunctionType :: String -> Type v -> Elab v (Type v, Type v)
expectFunctionType = expectMatch unArrow "_ -> _"

expectProductType :: String -> Type v -> Elab v (Type v, Type v)
expectProductType = expectMatch unProductT "(_, _)"
