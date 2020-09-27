module Facet.Name
( Name(..)
) where

import Data.Function (on)
import Prettyprinter (Pretty(..))

data Name = Name { name :: String, id' :: Int }

instance Eq Name where
  (==) = (==) `on` id'

instance Ord Name where
  compare = compare `on` id'

instance Show Name where
  showsPrec p = showsPrec p . pretty

instance Pretty Name where
  pretty n = pretty (name n) <> pretty (id' n)
