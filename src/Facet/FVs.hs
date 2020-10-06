module Facet.FVs
( FVs
, Scoped(..)
, prime
) where

import qualified Data.IntSet as IntSet
import           Data.Text (Text)
import           Facet.Name

type FVs = IntSet.IntSet


class Scoped t where
  fvs :: t -> FVs

instance Scoped IntSet.IntSet where
  fvs = id

instance Scoped Name where
  fvs = IntSet.singleton . id'


prime :: Scoped t => Text -> t -> Name
prime n t
  | IntSet.null fvs' = Name n 0
  | otherwise        = Name n (IntSet.findMax fvs' + 1)
  where
  fvs' = fvs t
