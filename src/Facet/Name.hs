module Facet.Name
( Name(..)
) where

import Prettyprinter (Pretty(..))

data Name = Name { name :: String, id' :: Int }

instance Pretty Name where
  pretty n = pretty (name n) <> pretty (id' n)
