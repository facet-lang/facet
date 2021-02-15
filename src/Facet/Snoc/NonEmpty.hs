module Facet.Snoc.NonEmpty
( NonEmpty(..)
) where

import Facet.Snoc

data NonEmpty a = Snoc a :|> a
  deriving (Eq, Foldable, Functor, Ord, Traversable)

infixl 5 :|>
