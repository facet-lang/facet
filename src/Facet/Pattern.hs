module Facet.Pattern
( -- * Patterns
  Pattern(..)
, ValPattern(..)
, _PWildcard
, _PVar
, _PCon
, EffPattern(..)
, fill
) where

import Data.Traversable (mapAccumL)
import Facet.Name
import Fresnel.Prism (Prism', prism')

-- Patterns

data Pattern a
  = PVal (ValPattern a)
  | PEff (EffPattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

_PVal :: Prism' (Pattern a) (ValPattern a)
_PVal = prism' PVal (\case
  PVal p -> Just p
  _      -> Nothing)

data ValPattern a
  = PWildcard
  | PVar a
  | PCon QName [ValPattern a]
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

_PWildcard :: Prism' (Pattern a) ()
_PWildcard = _PVal.prism' (const PWildcard) (\case
  PWildcard -> Just ()
  _         -> Nothing)

_PVar :: Prism' (Pattern a) a
_PVar = _PVal.prism' PVar (\case
  PVar a -> Just a
  _      -> Nothing)

_PCon :: Prism' (Pattern a) (QName, [ValPattern a])
_PCon = _PVal.prism' (uncurry PCon) (\case
  PCon h sp -> Just (h, sp)
  _         -> Nothing)


data EffPattern a = POp QName [ValPattern a] (ValPattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


-- | Fill a container with values computed sequentially from left to right.
fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)
