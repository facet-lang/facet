module Facet.Pattern
( -- * Patterns
  Pattern(..)
, ValPattern(..)
, _PWildcard
, _PVar
, _PCon
, fill
) where

import Data.Traversable (mapAccumL)
import Facet.Name
import Fresnel.Prism (Prism, Prism', prism, prism')

-- Patterns

data Pattern a
  = PVal (ValPattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

_PVal :: Prism (Pattern a) (Pattern b) (ValPattern a) (ValPattern b)
_PVal = prism PVal (\case
  PVal p -> Right p)

data ValPattern a
  = PWildcard
  | PVar a
  | PCon QName [Pattern a]
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

_PWildcard :: Prism' (Pattern a) ()
_PWildcard = _PVal.prism' (const PWildcard) (\case
  PWildcard -> Just ()
  _         -> Nothing)

_PVar :: Prism' (Pattern a) a
_PVar = _PVal.prism' PVar (\case
  PVar a -> Just a
  _      -> Nothing)

_PCon :: Prism' (Pattern a) (QName, [Pattern a])
_PCon = _PVal.prism' (uncurry PCon) (\case
  PCon h sp -> Just (h, sp)
  _         -> Nothing)


fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)
