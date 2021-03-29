module Facet.Usage
( -- * Quantities
  Quantity
  -- * Usage
, Usage(..)
, singleton
, lookup
, restrict
, withoutVars
) where

import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Facet.Name
import           Facet.Semiring
import qualified Facet.Vars as Vars
import           Prelude hiding (lookup)

-- Quantities

type Quantity = Few


-- Usage

newtype Usage = Usage (IntMap.IntMap (Map.Map Name Quantity))

instance Semigroup Usage where
  Usage a <> Usage b = Usage (IntMap.unionWith (<>) a b)

instance Monoid Usage where
  mempty = Usage mempty

instance LeftModule Quantity Usage where
  q ><< Usage a = Usage (fmap (q ><) <$> a)

singleton :: LName Level -> Quantity -> Usage
singleton (LName (Level i) n) q = Usage (IntMap.singleton i (Map.singleton n q))

lookup :: LName Level -> Usage -> Quantity
lookup (LName (Level i) n) (Usage a) = fromMaybe zero (Map.lookup n =<< IntMap.lookup i a)

restrict :: Usage -> Vars.Vars -> Usage
restrict (Usage u) (Vars.Vars v) = Usage (u `IntMap.restrictKeys` v)

withoutVars :: Usage -> Vars.Vars -> Usage
withoutVars (Usage u) (Vars.Vars v) = Usage (u `IntMap.withoutKeys` v)
