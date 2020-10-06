module Facet.FVs
( FVs
, null
, Scoped(..)
, prime
) where

import qualified Data.IntSet as IntSet
import           Data.Text (Text)
import           Facet.Name
import           Prelude hiding (null)

type FVs = IntSet.IntSet

null :: FVs -> Bool
null = IntSet.null


class Scoped t where
  fvs :: t -> FVs

instance Scoped IntSet.IntSet where
  fvs = id

instance Scoped Name where
  fvs = IntSet.singleton . id'


prime :: Scoped t => Text -> t -> Name
prime n t
  | null fvs' = Name n 0
  | otherwise = Name n (IntSet.findMax fvs' + 1)
  where
  fvs' = fvs t
