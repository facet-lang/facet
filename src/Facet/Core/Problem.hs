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

data Err v = Mismatch (Problem v) (Problem v)

newtype Solve v a = Solve { runSolve :: forall sig m . Has (Throw (Err v)) sig m => m a }


data Problem a
  = Type
  | (UName ::: Problem a) :=> (Problem a -> Solve a (Problem a))
  | Lam [(Pattern UName, Pattern (Problem a) -> Solve a (Problem a))]
  | Head a :$ Stack (Problem a)
  | Ex (Problem a) (Problem a -> Solve a (Problem a))

infixr 0 :=>
infixl 9 :$


data Head a
  = Global QName
  | Local a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
