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
import Facet.Core.Pattern
import Facet.Name hiding (L, R)
import Facet.Stack
import Facet.Syntax
import GHC.Stack (HasCallStack)

data Err v
  = Problem v :=/=: Problem v
  | UnsolvedMeta Meta

infix 1 :=/=:


newtype Solve v a = Solve { runSolve :: ST v (Either (Err v) a) }
  deriving (Functor)

instance Applicative (Solve v) where
  pure a = Solve $ pure (pure a)
  Solve f <*> Solve a = Solve (liftA2 (<*>) f a)

instance Monad (Solve v) where
  Solve m >>= f = Solve $ m >>= either (pure . throwError) (runSolve . f)

instance Algebra (Throw (Err v)) (Solve v) where
  alg _ (Throw e) _ = Solve $ pure (Left e)


data Problem a
  = Type
  | (UName ::: Problem a) :=> (Problem a -> Solve a (Problem a))
  | Lam [(Pattern UName, Pattern (Problem a) -> Solve a (Problem a))]
  | Head a :$ Stack (Problem a)
  | Let (UName := Problem a ::: Problem a) (Problem a -> Solve a (Problem a))

infixr 1 :=>
infixl 9 :$


newtype Meta = Meta { getMeta :: Int }
  deriving (Eq, Ord, Show)

zeroMeta :: Meta
zeroMeta = Meta 0

incrMeta :: Meta -> Meta
incrMeta = Meta . (+ 1) . getMeta

data Head a
  = Global QName
  | Local a
  | Metavar Meta
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unHead :: (QName -> b) -> (a -> b) -> (Meta -> b) -> Head a -> b
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

meta :: Meta -> Problem a
meta = var . Metavar


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
unify p = go (\ (_ := v) -> pure v) zeroMeta p -- FIXME: this should probably be an error about solving a metavariable nonlocally or something
  where
  go
    :: Eq v
    => (Meta := Problem v -> Solve v (Problem v))
    -> Meta
    -> Problem v :===: Problem v
    -> Solve v (Problem v)
  go k i = \case
    Type :===: Type -> pure Type
    t1 :=> b1 :===: t2 :=> b2 -> do
      _T' <- go k i (ty t1 :===: ty t2)
      pure $ tm t1 ::: _T' :=> \ v -> do
        _B1' <- b1 v
        _B2' <- b2 v
        go k i (_B1' :===: _B2')
    t :=> b :===: x -> do
      -- FIXME: solve metavars.
      -- FIXME: how do we communicate a solution?
      -- - statefully, we’d write the solution to a substitution, continue unifying, and at the end substitute all the metavars at once
      -- - locally, we could listen for the solution and either apply it or push the existential outwards.
      -- - listening sounds like some sort of coroutining thing?
      -- - unify could return the set of solved metas, but communicating that from the body of a binder outwards sounds tricky
      -- FIXME: how do we eliminate type lambdas in the value? we don’t _have_ the value here, so we can’t apply the meta.
      -- FIXME: shouldn’t something know about the type?
      _B' <- b (meta i)
      go k (incrMeta i) (_B' :===: x)
    f1 :$ as1 :===: f2 :$ as2
      | f1 == f2
      , length as1 == length as2 -> do
        as' <- traverse (go k i) (zipWith (:===:) (toList as1) (toList as2))
        unHead global bound meta f1 $$* as'
    Metavar n1 :$ Nil :===: x ->
      k (n1 := x)
    x :===: Metavar n2 :$ Nil ->
      k (n2 := x)
    Let (n1 := v1 ::: t1) b1 :===: Let (_ := v2 ::: t2) b2 -> do
      _T' <- go k i (t1 :===: t2)
      v' <- go k i (v1 :===: v2)
      pure $ Let (n1 := v' ::: _T') $ \ v -> do
        _B1' <- b1 v
        _B2' <- b2 v
        go k i (_B1' :===: _B2')
    t1 :===: t2 -> throwError $ t1 :=/=: t2


case' :: HasCallStack => Problem a -> [(Pattern UName, Pattern (Problem a) -> Solve a (Problem a))] -> Solve a (Problem a)
case' s ps = case getFirst (foldMap (\ (p, f) -> First $ f <$> match s p) ps) of
  Just v -> v
  _      -> error "non-exhaustive patterns in lambda"

match :: Problem a -> Pattern UName -> Maybe (Pattern (Problem a))
match s = \case
  Wildcard -> Just Wildcard
  Var _    -> Just (Var s)
  _        -> Nothing
