module Facet.Name
( Name(..)
, prime
, __
, Scoped(..)
, binder
) where

import           Data.Function (on)
import qualified Data.Text as T
import           Prettyprinter (Pretty(..))

data Name = Name { name :: T.Text, id' :: Int }

instance Eq Name where
  (==) = (==) `on` id'

instance Ord Name where
  compare = compare `on` id'

instance Show Name where
  showsPrec p = showsPrec p . pretty

instance Pretty Name where
  pretty n
    | T.null (name n) = var (id' n)
    | otherwise       = pretty (name n) <> pretty (id' n)
    where
    var = varFrom ['a'..'z']
    varFrom alpha i = pretty (toAlpha alpha i)
    toAlpha alphabet i = alphabet !! r : if q > 0 then show q else ""
      where
      n = length alphabet
      (q, r) = i `divMod` n


prime :: T.Text -> Int -> Name
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
  -> T.Text
  -> (t -> t)
  -> r
binder bound ctor n e = ctor n' b'
  where
  b' = e (bound n')
  n' = prime n (maxBV b')
