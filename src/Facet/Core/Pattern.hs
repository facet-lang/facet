module Facet.Core.Pattern
( -- * Patterns
  ValuePattern(..)
, EffectPattern(..)
, Pattern(..)
, pvar
, pcon
, peff
, fill
) where

import Data.Traversable (mapAccumL)
import Facet.Name
import Facet.Snoc

-- Patterns

data ValuePattern a
  = PWildcard
  | PVar a
  | PCon RName (Snoc (ValuePattern a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data EffectPattern a
  = PAll a
  | POp RName (Snoc (ValuePattern a)) a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Pattern a
  = PEff (EffectPattern a)
  | PVal (ValuePattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

pvar :: a -> Pattern a
pvar = PVal . PVar

pcon :: RName -> Snoc (ValuePattern a) -> Pattern a
pcon n fs = PVal $ PCon n fs

peff :: RName -> Snoc (ValuePattern a) -> a -> Pattern a
peff o vs k = PEff $ POp o vs k


fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)
