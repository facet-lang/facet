{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.FVs
( FVs(..)
, singleton
, insert
, delete
, difference
, member
, Scoped(..)
, prime
) where

import           Data.Coerce
import qualified Data.IntSet as IntSet
import           Data.Text (Text)
import           Facet.Name

newtype FVs = FVs { getFVs :: IntSet.IntSet }
  deriving (Monoid, Semigroup, Show)

singleton :: Name -> FVs
singleton = FVs . IntSet.singleton . id'

insert :: Name -> FVs -> FVs
insert = coerce (IntSet.insert . id')

delete :: Name -> FVs -> FVs
delete = coerce (IntSet.delete . id')

difference :: FVs -> FVs -> FVs
difference = coerce IntSet.difference

member :: Name -> FVs -> Bool
member = coerce (IntSet.member . id')


class Scoped t where
  fvs :: t -> FVs

instance Scoped FVs where
  fvs = id

instance Scoped Name where
  fvs = singleton


prime :: Scoped t => Text -> t -> Name
prime n = Name n . maybe 0 (+ 1) . findMax' . getFVs . fvs


findMax' :: IntSet.IntSet -> Maybe Int
findMax' s
  | IntSet.null s = Nothing
  | otherwise     = Just (IntSet.findMax s)
