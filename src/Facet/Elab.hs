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
, Context
, Val
, Type
, Expr
, Elab(..)
, Check(..)
, Synth(..)
, check
, unify
, Metacontext(..)
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
import           Data.Functor.Identity
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Text as T
import           Data.Traversable (for)
import           Facet.Context hiding (getMetacontext)
import qualified Facet.Core.Module as CM
import qualified Facet.Core.Pattern as CP
import           Facet.Core.Value hiding (bound, global, ($$))
import qualified Facet.Core.Value as CV
import qualified Facet.Env as Env
import           Facet.Name (DName, Index(..), QName(..), UName)
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

type I = Identity
type Val = Value I
type Type = Value I
type Expr = Value I
type Prob v = Value (M v) v

newtype M v a = M { rethrow :: forall sig m . Has (State (Metacontext (Val v ::: Type v)) :+: Throw (Err v)) sig m => m a }

instance Functor (M v) where
  fmap f (M m) = M (fmap f m)

instance Applicative (M v) where
  pure a = M $ pure a
  M f <*> M a = M (f <*> a)

instance Monad (M v) where
  M m >>= f = M $ m >>= rethrow . f

instance Algebra (State (Metacontext (Val v ::: Type v)) :+: Throw (Err v)) (M v) where
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


newtype Unify v a = Unify { runUnify :: forall sig m . Has (Reader (Env.Env (Type v)) :+: Reader (Context (Val v ::: Type v)) :+: Reader Span :+: State (Metacontext (Val v ::: Type v)) :+: Throw (Err v)) sig m => m a }

instance Functor (Unify v) where
  fmap f (Unify m) = Unify (fmap f m)

instance Applicative (Unify v) where
  pure a = Unify $ pure a
  Unify f <*> Unify a = Unify (f <*> a)

instance Monad (Unify v) where
  Unify m >>= f = Unify $ m >>= runUnify . f

instance Algebra (Reader (Env.Env (Type v)) :+: Reader (Context (Val v ::: Type v)) :+: Reader Span :+: State (Metacontext (Val v ::: Type v)) :+: Throw (Err v)) (Unify v) where
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

getMetacontext :: Has (State (Metacontext (Val v ::: Type v))) sig (t v) => t v (Metacontext (Val v ::: Type v))
getMetacontext = get



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
unify (t1 :===: t2) = do
  let t1' = run $ handle t1
      t2' = run $ handle t2
  evalState (Metacontext @(Val v ::: Type v) []) . runUnify $ go (t1' :===: t2')
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
    f1 :$ a1   :===: f2 :$ a2
      | f1 == f2
      , Just a <- unifyS (a1 :===: a2) -> (f1 :$) <$> a
    a1 :-> b1  :===: a2 :-> b2  -> (:->) <$> go (a1 :===: a2) <*> go (b1 :===: b2)
    t1 :=> b1  :===: t2 :=> b2  -> do
      t <- go (ty t1 :===: ty t2)
      b <- tm t1 ::: t |- \ v -> do
        let v' = run (handle v)
        b1' <- rethrow $ b1 v'
        b2' <- rethrow $ b2 v'
        go (b1' :===: b2')
      pure $ tm t1 ::: t :=> b
    TPrd l1 r1 :===: TPrd l2 r2 -> TPrd <$> go (l1 :===: l2) <*> go (r1 :===: r2)
    Prd  l1 r1 :===: Prd  l2 r2 -> Prd  <$> go (l1 :===: l2) <*> go (r1 :===: r2)
    -- FIXME: build and display a diff of the root types
    t1 :===: t2                       -> do
      t1' <- rethrow $ handle t1
      t2' <- rethrow $ handle t2
      couldNotUnify t1' t2'
  unifyS (Nil      :===: Nil)      = Just (pure Nil)
  unifyS (i1 :> l1 :===: i2 :> l2) = liftA2 (:>) <$> unifyS (i1 :===: i2) <*> Just (go (l1 :===: l2))
  unifyS _                         = Nothing


-- FIXME: is it possible to do something clever with delimited continuations or coroutines to bind variables outside our scope?


meta :: UName ::: Val v ::: Type v -> Unify v (Type v)
meta t = do
  mctx <- getMetacontext
  put (t <| mctx)
  pure $ CV.metavar (metalevel mctx)


-- General

switch
  :: Eq v
  => Synth v a
  -> Maybe (Type v)
  -> Elab v (a ::: Type v)
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
  pure $ run (f' CV.$$ a') ::: _B


(|-)
  :: Has (Reader (Context (Val v ::: Type v))) sig (t v)
  => UName ::: Type v
  -> (Val v -> t v (Val v))
  -> t v (Val v -> I (Val v))
n ::: _T |- f = do
  ctx <- askContext
  handleBinder (level ctx) (\ v -> local (|> (n ::: v ::: _T)) (f v))

infix 1 |-

(|-*)
  :: Has (Reader (Context (Val v ::: Type v))) sig (t v)
  => CP.Pattern (UName ::: Type v)
  -> (CP.Pattern (Val v) -> t v (Val v))
  -> t v (CP.Pattern (Val v) -> I (Val v))
p |-* f = do
  ctx <- askContext
  handleBinderP (level ctx) p (\ v ->
    local (flip (foldl' (|>)) (zipWith (\ (n ::: _T) v -> n ::: v ::: _T) (toList p) (toList v))) (f v))

infix 1 |-*


-- Types

elabType
  :: (HasCallStack, Eq v)
  => Spanned (ST.Type Spanned a)
  -> Maybe (Type v)
  -> Elab v (Type v ::: Type v)
elabType = withSpan' $ \case
  ST.Free  n -> switch $ global n
  ST.Bound n -> switch $ bound n
  ST.Hole  n -> check (hole n) "hole"
  ST.Type    -> switch $ _Type
  ST.Void    -> switch $ _Void
  ST.Unit    -> switch $ _Unit
  t ST.:=> b -> switch $ fmap (checkElab . elabType) t >~> checkElab (elabType b)
  f ST.:$  a -> switch $ synthElab (elabType f) $$  checkElab (elabType a)
  a ST.:-> b -> switch $ checkElab (elabType a) --> checkElab (elabType b)
  l ST.:*  r -> switch $ checkElab (elabType l) .*  checkElab (elabType r)
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
    let _B' = run (_B v)
    check (b ::: _B')
  pure (TLam n b')

lam
  :: UName
  -> Check v (Expr v)
  -> Check v (Expr v)
lam n b = Check $ \ _T -> do
  (_A, _B) <- expectFunctionType "when checking lambda" _T
  -- FIXME: shouldn’t we use the bound variable?
  b' <- CP.Var (n ::: _A) |-* \ v -> check (b ::: _B)
  pure (Lam [(CP.Var n, b')])

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
  -- FIXME: this shape makes it hard to elaborate nested pattern matches, because we kind of need to transpose the table.
  -- e.g. in xor : Bool -> Bool -> Bool { False True -> True, True False -> True, _ _ -> False }, we should have the second column of cases appearing under each of the first, or else we’re inserting inexhaustive patterns
  SE.Clauses cs -> Check $ \ _T -> do
    (_A, _B) <- expectFunctionType "when checking clauses" _T
    Lam <$> case cs of
      [] -> [] <$ unify (_A :===: Void)
      cs -> traverse (uncurry (clause _A _B)) cs
  where
  clause _A _B (p:|ps) b = do
    p' <- check (elabPattern p ::: _A)
    -- FIXME: shouldn’t we use the bound variable(s)?
    b' <- p' |-* \ v -> check (go ps b ::: _B)
    pure (tm <$> p', b')
  go []     b = checkElab (elabExpr b)
  go (p:ps) b = Check $ \ _T -> do
    (_A, _B) <- expectFunctionType "when checking clause" _T
    Lam . pure <$> clause _A _B (p:|ps) b


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
      Nil      -> Nil      <$  unify (TUnit :===: _T)
      Nil :> p -> (Nil :>) <$> check (elabPattern p ::: _T)
      ps  :> p -> do
        (_L, _R) <- expectProductType "when checking tuple pattern" _T
        (:>) <$> go _L ps <*> check (elabPattern p ::: _R)


-- Declarations

elabDecl
  :: (HasCallStack, Eq v)
  => Spanned (SD.Decl Spanned a)
  -> Check v (Expr v) ::: Check v (Type v)
elabDecl = withSpans $ \case
  (n ::: t) SD.:=> b ->
    let b' ::: _B = elabDecl b
    in tlam n b' ::: checkElab (switch (n ::: checkElab (elabType t) >~> _B))

  (n ::: t) SD.:-> b ->
    let b' ::: _B = elabDecl b
    -- FIXME: types and terms are bound with the same context, so the indices in the type are incremented, but arrow types don’t extend the context, so we were mishandling them.
    in lam n b' ::: checkElab (switch (checkElab (elabType t) --> local (|> (n ::: (Type `asParameterOf` b') ::: (Type `asParameterOf` b'))) _B))

  t SD.:= b ->
    checkElab (elabExpr b) ::: checkElab (elabType t)
  where
  withSpans f (s, d) = let t ::: _T = f d in setSpan s t ::: setSpan s _T

  asParameterOf :: a -> f a -> a
  asParameterOf = const


-- Modules

elabModule
  :: forall v a m sig
  .  (HasCallStack, Has (Throw (Err v)) sig m, Eq v)
  => Spanned (SM.Module Spanned a)
  -> m (CM.Module I v)
elabModule (s, SM.Module mname ds) = runReader s . evalState (mempty @(Env.Env (Type v))) $ do
  -- FIXME: elaborate all the types first, and only then the terms
  -- FIXME: maybe figure out the graph for mutual recursion?
  defs <- for ds $ \ (s, (n, d)) -> setSpan s $ do
    env <- get @(Env.Env (Type v))
    e' ::: _T <- runReader @(Context (Val v ::: Type v)) empty . runReader env $ do
      let e ::: t = elabDecl d
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

expectQuantifiedType :: String -> Type v -> Elab v (UName ::: Type v, Type v -> I (Type v))
expectQuantifiedType = expectMatch unForAll "{_} -> _"

expectFunctionType :: String -> Type v -> Elab v (Type v, Type v)
expectFunctionType = expectMatch unArrow "_ -> _"

expectProductType :: String -> Type v -> Elab v (Type v, Type v)
expectProductType = expectMatch unProductT "(_, _)"
