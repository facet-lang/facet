module Facet.Name
( Name(..)
, prime
, Scoped(..)
) where

import Data.Function (on)
import Data.Text (Text)
import Prettyprinter (Pretty(..))

data Name = Name { name :: Text, id' :: Int }

instance Eq Name where
  (==) = (==) `on` id'

instance Ord Name where
  compare = compare `on` id'

instance Show Name where
  showsPrec p = showsPrec p . pretty

instance Pretty Name where
  pretty n = pretty (name n) <> pretty (id' n)

prime :: Name -> Name
prime n = n{ id' = id' n + 1 }


class Scoped t where
  maxBV :: t -> Int

instance Scoped Name where
  maxBV = id'
