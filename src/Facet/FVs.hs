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
prime n = Name n . maybe 0 (+ 1) . findMax' . fvs

findMax' :: IntSet.IntSet -> Maybe Int
findMax' s
  | IntSet.null s = Nothing
  | otherwise     = Just (IntSet.findMax s)
