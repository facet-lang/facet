module Facet.Vars
( -- * Vars
  Vars(..)
) where

import qualified Data.IntSet as IntSet

-- Vars

newtype Vars = Vars IntSet.IntSet
