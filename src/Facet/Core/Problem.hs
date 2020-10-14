{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Problem
( Problem(..)
, Head(..)
) where

import Facet.Core.Pattern
import Facet.Name
import Facet.Stack
import Facet.Syntax

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
