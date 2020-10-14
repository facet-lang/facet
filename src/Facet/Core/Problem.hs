{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Problem
( Solve(..)
, Err(..)
, Problem(..)
, Head(..)
) where

import Control.Effect.Throw
import Facet.Core.Pattern
import Facet.Name
import Facet.Stack
import Facet.Syntax

data Err v = Mismatch (Problem (Solve v) v) (Problem (Solve v) v)

newtype Solve v a = Solve { runSolve :: forall sig m . Has (Throw (Err v)) sig m => m a }


data Problem m a
  = Type
  | (UName ::: Problem m a) :=> (Problem m a -> m (Problem m a))
  | Lam [(Pattern UName, Pattern (Problem m a) -> m (Problem m a))]
  | Head a :$ Stack (Problem m a)
  | Ex (Problem m a) (Problem m a -> m (Problem m a))

infixr 0 :=>
infixl 9 :$


data Head a
  = Global QName
  | Local a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
