module Facet.Pattern.Column
( Column(..)
) where

import qualified Data.IntMap as IntMap

newtype Column a = Column { getColumn :: IntMap.IntMap a }
