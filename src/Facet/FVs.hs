module Facet.FVs
( FVs
, Scoped(..)
) where

import qualified Data.IntSet as IntSet

type FVs = IntSet.IntSet


class Scoped t where
  fvs :: t -> FVs

instance Scoped IntSet.IntSet where
  fvs = id
