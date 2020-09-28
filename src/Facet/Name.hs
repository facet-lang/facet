module Facet.Name
( Name(..)
, prime
, __
, Scoped(..)
, binder
) where

import Data.Function (on)
import Data.Text (Text, pack)
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

prime :: Text -> Int -> Name
prime n i = Name n (i + 1)


__ :: T.Text
__ = T.empty


class Scoped t where
  maxBV :: t -> Int

instance Scoped Name where
  maxBV = id'

binder
  :: Scoped t
  => (Name -> t)
  -> (Name -> t -> r)
  -> Text
  -> (t -> t)
  -> r
binder bound ctor n e = ctor n' b'
  where
  b' = e (bound n')
  n' = prime n (maxBV b')
