module Facet.Core.Pattern
( -- * Patterns
  Pattern(..)
, fill
) where

import Data.Traversable (mapAccumL)
import Facet.Name
import Facet.Snoc

-- Patterns

data Pattern a
  = PWildcard
  | PVar a
  | PCon RName (Snoc (Pattern a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)
