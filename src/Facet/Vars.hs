{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Vars
( Vars(..)
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

newtype Vars = Vars { getVars :: IntSet.IntSet }
  deriving (Monoid, Semigroup, Show)

singleton :: Name -> Vars
singleton = Vars . IntSet.singleton . id'

insert :: Name -> Vars -> Vars
insert = coerce (IntSet.insert . id')

delete :: Name -> Vars -> Vars
delete = coerce (IntSet.delete . id')

difference :: Vars -> Vars -> Vars
difference = coerce IntSet.difference

member :: Name -> Vars -> Bool
member = coerce (IntSet.member . id')


class Scoped t where
  fvs :: t -> Vars

instance Scoped Vars where
  fvs = id

instance Scoped Name where
  fvs = singleton


prime :: Scoped t => Text -> t -> Name
prime n = Name n . maybe 0 (+ 1) . findMax' . getVars . fvs


findMax' :: IntSet.IntSet -> Maybe Int
findMax' s
  | IntSet.null s = Nothing
  | otherwise     = Just (IntSet.findMax s)
