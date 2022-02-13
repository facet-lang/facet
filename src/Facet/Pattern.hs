module Facet.Pattern
( -- * Patterns
  Pattern(..)
, _PWildcard
, fill
) where

import Data.Traversable (mapAccumL)
import Facet.Name
import Facet.Syntax
import Fresnel.Prism (Prism', prism')

-- Patterns

data Pattern a
  = PWildcard
  | PVar a
  | PCon RName [Pattern a]
  | PDict [RName :=: a]
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

_PWildcard :: Prism' (Pattern a) ()
_PWildcard = prism' (const PWildcard) (\case
  PWildcard -> Just ()
  _         -> Nothing)


fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)
