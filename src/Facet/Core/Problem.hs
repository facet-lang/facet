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
, Head(..)
, unHead
, global
) where

import Control.Algebra
import Control.Effect.Sum
import Control.Effect.Throw
import Facet.Core.Pattern
import Facet.Name
import Facet.Stack
import Facet.Syntax

data Err v = Mismatch (Problem v) (Problem v)

newtype Solve v a = Solve { runSolve :: forall sig m . Has (Throw (Err v)) sig m => m a }

instance Functor (Solve v) where
  fmap f (Solve m) = Solve (fmap f m)

instance Applicative (Solve v) where
  pure a = Solve $ pure a
  Solve f <*> Solve a = Solve (f <*> a)

instance Monad (Solve v) where
  Solve m >>= f = Solve $ m >>= runSolve . f

instance Algebra (Throw (Err v)) (Solve v) where
  alg hdl sig ctx = Solve $ alg (runSolve . hdl) (inj sig) ctx


data Problem a
  = Type
  | (UName ::: Problem a) :=> (Problem a -> Solve a (Problem a))
  | Lam [(Pattern UName, Pattern (Problem a) -> Solve a (Problem a))]
  | Head a :$ Stack (Problem a)
  | Ex (UName ::: Problem a) (Problem a -> Solve a (Problem a))
  | Let UName (Problem a ::: Problem a) (Problem a -> Solve a (Problem a))

infixr 0 :=>
infixl 9 :$


data Head a
  = Global QName
  | Local a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unHead :: (QName -> b) -> (a -> b) -> Head a -> b
unHead f g = \case
  Global n -> f n
  Local  n -> g n


global :: QName -> Problem a
global n = Global n :$ Nil
