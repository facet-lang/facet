module Facet.Usage
( -- * Quantities
  Quantity
  -- * Usage
, Usage(..)
, singleton
, lookupUsage
, restrictUsage
) where

import qualified Data.IntMap as IntMap
import           Data.Maybe (fromMaybe)
import           Facet.Name
import           Facet.Semiring
import           Facet.Vars

-- Quantities

type Quantity = Few


-- Usage

newtype Usage = Usage (IntMap.IntMap Quantity)

instance Semigroup Usage where
  Usage a <> Usage b = Usage (IntMap.unionWith (<>) a b)

instance Monoid Usage where
  mempty = Usage mempty

instance LeftModule Quantity Usage where
  q ><< Usage a = Usage ((q ><) <$> a)

singleton :: Level -> Quantity -> Usage
singleton (Level i) q = Usage (IntMap.singleton i q)

lookupUsage :: Level -> Usage -> Quantity
lookupUsage (Level i) (Usage a) = fromMaybe zero (IntMap.lookup i a)

restrictUsage :: Usage -> Vars -> Usage
restrictUsage (Usage u) (Vars v) = Usage (u `IntMap.restrictKeys` v)
