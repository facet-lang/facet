module Facet.Pattern.Column
( Column(..)
, column_
, RowIndex
) where

import qualified Data.IntMap as IntMap
import           Fresnel.Iso (Iso, coerced)

newtype Column a = Column { getColumn :: IntMap.IntMap a }
  deriving (Monoid)

column_ :: Iso (Column a) (Column b) (IntMap.IntMap a) (IntMap.IntMap b)
column_ = coerced
{-# INLINE column_ #-}

instance Semigroup a => Semigroup (Column a) where
  as <> bs = Column (IntMap.unionWith (<>) (getColumn as) (getColumn bs))

type RowIndex = Int
