module Facet.Vars
( -- * Vars
  Vars(..)
, singleton
) where

import qualified Data.IntSet as IntSet
import           Facet.Name

-- Vars

newtype Vars = Vars IntSet.IntSet

singleton :: Level -> Vars
singleton = Vars . IntSet.singleton . getLevel
