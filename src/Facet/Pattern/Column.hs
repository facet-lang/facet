module Facet.Pattern.Column
( Column(..)
, column_
) where

import qualified Data.IntMap as IntMap
import           Fresnel.Iso (Iso, coerced)

newtype Column a = Column { getColumn :: IntMap.IntMap a }

column_ :: Iso (Column a) (Column b) (IntMap.IntMap a) (IntMap.IntMap b)
column_ = coerced
{-# INLINE column_ #-}
