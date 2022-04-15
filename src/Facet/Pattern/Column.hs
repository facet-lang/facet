{-# LANGUAGE TypeFamilies #-}
module Facet.Pattern.Column
( Column(..)
, column_
, RowIndex
  -- * Constructors
, singleton
) where

import qualified Data.IntMap as IntMap
import           Fresnel.At
import           Fresnel.Iso (Iso, coerced)
import           Fresnel.Ixed

newtype Column a = Column { getColumn :: IntMap.IntMap a }
  deriving (Monoid)

column_ :: Iso (Column a) (Column b) (IntMap.IntMap a) (IntMap.IntMap b)
column_ = coerced
{-# INLINE column_ #-}

instance Semigroup a => Semigroup (Column a) where
  as <> bs = Column (IntMap.unionWith (<>) (getColumn as) (getColumn bs))

type RowIndex = Int

instance Ixed (Column a) where
  type Index (Column a) = RowIndex
  type IxValue (Column a) = a
  ix i = column_.ix i

instance At (Column a) where
  at i = column_.at i


-- Constructors

-- | Construct a sparse 'Column' from a single value.
singleton :: RowIndex -> a -> Column a
singleton row a = Column (IntMap.singleton row a)
{-# INLINE singleton #-}
