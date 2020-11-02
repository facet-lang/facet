module Facet.Stack.NonEmpty
( NonEmpty(..)
) where

import Facet.Stack

data NonEmpty a = Stack a :|> a
  deriving (Eq, Foldable, Functor, Ord, Traversable)

infixl 5 :|>
