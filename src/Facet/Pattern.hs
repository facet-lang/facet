module Facet.Pattern
( -- * Patterns
  Pattern(..)
, _PWildcard
, _PVar
, _PCon
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

_PVar :: Prism' (Pattern a) a
_PVar = prism' PVar (\case
  PVar a -> Just a
  _      -> Nothing)

_PCon :: Prism' (Pattern a) (RName, [Pattern a])
_PCon = prism' (uncurry PCon) (\case
  PCon h sp -> Just (h, sp)
  _         -> Nothing)


fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)
