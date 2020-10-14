{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Problem
( Solve(..)
, Err(..)
, Problem(..)
, Head(..)
, unHead
, global
-- , bound
, ($$)
, ($$*)
, unify
, case'
, match
) where

import Control.Algebra
import Control.Effect.State
import Control.Effect.Sum
import Control.Effect.Throw
import Data.Foldable (foldl', toList)
import Data.Monoid (First(..))
import Facet.Core.Pattern
import Facet.Name hiding (L, R)
import Facet.Stack
import Facet.Syntax
import GHC.Stack (HasCallStack)

data Err v
  = Problem v :=/=: Problem v
  | UnsolvedMeta Level

infix 1 :=/=:


type Subst v = [Maybe (Problem v) ::: Problem v]

newtype Solve v a = Solve { runSolve :: forall sig m . Has (State (Subst v) :+: Throw (Err v)) sig m => m a }
  deriving (Functor)

instance Applicative (Solve v) where
  pure a = Solve $ pure a
  Solve f <*> Solve a = Solve (f <*> a)

instance Monad (Solve v) where
  Solve m >>= f = Solve $ m >>= runSolve . f

instance Algebra (State (Subst v) :+: Throw (Err v)) (Solve v) where
  alg hdl sig ctx = case sig of
    L subst -> Solve $ alg (runSolve . hdl) (inj subst) ctx
    R throw -> Solve $ alg (runSolve . hdl) (inj throw) ctx


data Problem a
  = Type
  | (UName ::: Problem a) :=> (Problem a -> Solve a (Problem a))
  | Lam [(Pattern UName, Pattern (Problem a) -> Solve a (Problem a))]
  | Head a :$ Stack (Problem a)

infixr 1 :=>
infixl 9 :$


data Head a
  = Global QName
  | Local a
  | Metavar Level
  deriving (Eq)

unHead :: (QName -> b) -> (a -> b) -> (Level -> b) -> Head a -> b
unHead f g h = \case
  Global  n -> f n
  Local   n -> g n
  Metavar n -> h n


var :: Head a -> Problem a
var = (:$ Nil)

global :: QName -> Problem a
global = var . Global

bound :: a -> Problem a
bound = var . Local

metavar :: Level -> Problem a
metavar = var . Metavar


($$) :: HasCallStack => Problem a -> Problem a -> Solve a (Problem a)
(f :$ as) $$ a = pure (f :$ (as :> a))
(_ :=> b) $$ a = b a
Lam    ps $$ a = case' a ps
_         $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Problem a -> t (Problem a) -> Solve a (Problem a)
f $$* as = foldl' (\ f a -> f >>= ($$ a)) (pure f) as

infixl 9 $$, $$*


unify
  :: Eq a
  => Problem a :===: Problem a
  -> Solve a (Problem a)
unify = go
  where
  go
    :: Eq v
    => Problem v :===: Problem v
    -> Solve v (Problem v)
  go = \case
    Type :===: Type -> pure Type
    t1 :=> b1 :===: t2 :=> b2 -> do
      _T' <- go (ty t1 :===: ty t2)
      pure $ tm t1 ::: _T' :=> \ v -> do
        _B1' <- b1 v
        _B2' <- b2 v
        go (_B1' :===: _B2')
    t :=> b :===: x -> do
      -- FIXME: how do we eliminate type lambdas in the value? we don’t _have_ the value here, so we can’t apply the meta.
      v <- meta (ty t)
      _B' <- b (metavar v)
      go (_B' :===: x)
    f1 :$ as1 :===: f2 :$ as2
      | f1 == f2
      , length as1 == length as2 -> do
        as' <- traverse go (zipWith (:===:) (toList as1) (toList as2))
        unHead global bound metavar f1 $$* as'
    Metavar n1 :$ Nil :===: x ->
      solve (n1 := x)
    x :===: Metavar n2 :$ Nil ->
      solve (n2 := x)
    t1 :===: t2 -> throwError $ t1 :=/=: t2

  meta _T = do
    subst <- getSubst
    put ((Nothing ::: _T):subst)
    pure (Level (length subst))
  solve :: Eq v => Level := Problem v -> Solve v (Problem v)
  solve (m := val') = do
    subst <- getSubst
    let n = levelToIndex (Level (length subst)) m
    -- FIXME: occurs check
    case subst !! getIndex n of
      Just val ::: _T -> go (val :===: val')
      Nothing  ::: _T -> val' <$ put (insertSubst n (val' ::: _T) subst)
  getSubst :: Solve v (Subst v)
  getSubst = get

  insertSubst :: Index -> Problem v ::: Problem v -> Subst v -> Subst v
  insertSubst n (v ::: _T) s = take (getIndex n - 1) s <> ((Just v ::: _T) : drop (getIndex n) s)



case' :: HasCallStack => Problem a -> [(Pattern UName, Pattern (Problem a) -> Solve a (Problem a))] -> Solve a (Problem a)
case' s ps = case getFirst (foldMap (\ (p, f) -> First $ f <$> match s p) ps) of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Problem a -> Pattern UName -> Maybe (Pattern (Problem a))
match s = \case
  Wildcard -> Just Wildcard
  Var _    -> Just (Var s)
  _        -> Nothing
