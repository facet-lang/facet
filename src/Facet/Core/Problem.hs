{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Problem
( Solve(..)
, Err(..)
, Problem(..)
, Meta(..)
, Head(..)
, unHead
, global
, bound
, ($$)
, ($$*)
, unify
, case'
, match
) where

import Control.Algebra
import Control.Applicative (liftA2)
import Control.Effect.Throw
import Control.Monad.ST
import Data.Foldable (foldl', toList)
import Data.Monoid (First(..))
import Data.STRef
import Facet.Core.Pattern
import Facet.Name hiding (L, R)
import Facet.Stack
import Facet.Syntax
import GHC.Stack (HasCallStack)

data Err s v
  = Problem s v :=/=: Problem s v
  | UnsolvedMeta (Meta s v)

infix 1 :=/=:


newtype Solve s v a = Solve { runSolve :: ST s (Either (Err s v) a) }
  deriving (Functor)

instance Applicative (Solve s v) where
  pure a = Solve $ pure (pure a)
  Solve f <*> Solve a = Solve (liftA2 (<*>) f a)

instance Monad (Solve s v) where
  Solve m >>= f = Solve $ m >>= either (pure . throwError) (runSolve . f)

instance Algebra (Throw (Err s v)) (Solve s v) where
  alg _ (Throw e) _ = Solve $ pure (Left e)


data Problem s a
  = Type
  | (UName ::: Problem s a) :=> (Problem s a -> Solve s a (Problem s a))
  | Lam [(Pattern UName, Pattern (Problem s a) -> Solve s a (Problem s a))]
  | Head s a :$ Stack (Problem s a)

infixr 1 :=>
infixl 9 :$


newtype Meta s a = Meta { getMeta :: STRef s (Maybe (Problem s a) ::: Problem s a) }
  deriving (Eq)

data Head s a
  = Global QName
  | Local a
  | Metavar (Meta s a)
  deriving (Eq)

unHead :: (QName -> b) -> (a -> b) -> (Meta s a -> b) -> Head s a -> b
unHead f g h = \case
  Global  n -> f n
  Local   n -> g n
  Metavar n -> h n


var :: Head s a -> Problem s a
var = (:$ Nil)

global :: QName -> Problem s a
global = var . Global

bound :: a -> Problem s a
bound = var . Local

metavar :: Meta s a -> Problem s a
metavar = var . Metavar


($$) :: HasCallStack => Problem s a -> Problem s a -> Solve s a (Problem s a)
(f :$ as) $$ a = pure (f :$ (as :> a))
(_ :=> b) $$ a = b a
Lam    ps $$ a = case' a ps
_         $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (HasCallStack, Foldable t) => Problem s a -> t (Problem s a) -> Solve s a (Problem s a)
f $$* as = foldl' (\ f a -> f >>= ($$ a)) (pure f) as

infixl 9 $$, $$*


unify
  :: Eq a
  => Problem s a :===: Problem s a
  -> Solve s a (Problem s a)
unify p = go p
  where
  go
    :: Eq v
    => Problem s v :===: Problem s v
    -> Solve s v (Problem s v)
  go = \case
    Type :===: Type -> pure Type
    t1 :=> b1 :===: t2 :=> b2 -> do
      _T' <- go (ty t1 :===: ty t2)
      pure $ tm t1 ::: _T' :=> \ v -> do
        _B1' <- b1 v
        _B2' <- b2 v
        go (_B1' :===: _B2')
    t :=> b :===: x -> do
      -- FIXME: solve metavars.
      -- FIXME: how do we communicate a solution?
      -- - statefully, we’d write the solution to a substitution, continue unifying, and at the end substitute all the metavars at once
      -- - locally, we could listen for the solution and either apply it or push the existential outwards.
      -- - listening sounds like some sort of coroutining thing?
      -- - unify could return the set of solved metas, but communicating that from the body of a binder outwards sounds tricky
      -- FIXME: how do we eliminate type lambdas in the value? we don’t _have_ the value here, so we can’t apply the meta.
      -- FIXME: shouldn’t something know about the type?
      v <- meta (ty t)
      _B' <- b (metavar v)
      go (_B' :===: x)
    f1 :$ as1 :===: f2 :$ as2
      | f1 == f2
      , length as1 == length as2 -> do
        as' <- traverse (go) (zipWith (:===:) (toList as1) (toList as2))
        unHead global bound metavar f1 $$* as'
    Metavar n1 :$ Nil :===: x ->
      solve (n1 := x)
    x :===: Metavar n2 :$ Nil ->
      solve (n2 := x)
    t1 :===: t2 -> throwError $ t1 :=/=: t2

  meta _T = Solve (Right . Meta <$> newSTRef (Nothing ::: _T))
  solve :: Eq v => Meta s v := Problem s v -> Solve s v (Problem s v)
  solve (Meta ref := val') = Solve $ do
    val ::: _T <- readSTRef ref
    -- FIXME: occurs check
    case val of
      Just val -> runSolve (go (val :===: val'))
      Nothing  -> Right val' <$ writeSTRef ref (Just val' ::: _T)


case' :: HasCallStack => Problem s a -> [(Pattern UName, Pattern (Problem s a) -> Solve s a (Problem s a))] -> Solve s a (Problem s a)
case' s ps = case getFirst (foldMap (\ (p, f) -> First $ f <$> match s p) ps) of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Problem s a -> Pattern UName -> Maybe (Pattern (Problem s a))
match s = \case
  Wildcard -> Just Wildcard
  Var _    -> Just (Var s)
  _        -> Nothing
