module Facet.Core
( -- * Patterns
  ValuePattern(..)
, Pattern(..)
, pvar
, pcon
, fill
) where

import Data.Traversable (mapAccumL)
import Facet.Name
import Facet.Stack
import Facet.Syntax
import Prelude hiding (zip, zipWith)

-- Patterns

data ValuePattern a
  = PWildcard
  | PVar a
  | PCon (Q Name :$ ValuePattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Pattern a
  = PEff (Q Name) (Stack (Pattern a)) a
  | PAll a
  | PVal (ValuePattern a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

pvar :: a -> Pattern a
pvar = PVal . PVar

pcon :: Q Name :$ ValuePattern a -> Pattern a
pcon = PVal . PCon


fill :: Traversable t => (b -> (b, c)) -> b -> t a -> (b, t c)
fill f = mapAccumL (const . f)
