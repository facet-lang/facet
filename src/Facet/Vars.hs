{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Vars
( Vars(..)
, insert
, delete
, difference
, member
, Binding(..)
, Scoped(..)
, FVs(..)
, prime
) where

import           Data.Coerce
import qualified Data.IntSet as IntSet
import           Data.Text (Text)
import           Facet.Name

newtype Vars = Vars { getVars :: IntSet.IntSet }
  deriving (Monoid, Semigroup, Show)

insert :: Name -> Vars -> Vars
insert = coerce (IntSet.insert . id')

delete :: Name -> Vars -> Vars
delete = coerce (IntSet.delete . id')

difference :: Vars -> Vars -> Vars
difference = coerce IntSet.difference

member :: Name -> Vars -> Bool
member = coerce (IntSet.member . id')


class Monoid t => Binding t where
  singleton :: Name -> t
  bind :: Name -> t -> t

instance Binding Vars where
  singleton = Vars . IntSet.singleton . id'
  bind = delete


class Scoped t where
  fvs :: t -> Vars

instance Scoped Vars where
  fvs = id

instance Scoped Name where
  fvs = singleton


newtype FVs = FVs { runFVs :: Vars -> Vars -> Vars }

instance Semigroup FVs where
  FVs v1 <> FVs v2 = FVs $ \ b f -> v1 b (v2 b f)

instance Monoid FVs where
  mempty = FVs (const id)

instance Binding FVs where
  singleton n = FVs $ \ b -> if n `member` b then id else insert n
  bind n v = FVs $ runFVs v . insert n


prime :: Scoped t => Text -> t -> Name
prime n = Name n . maybe 0 (+ 1) . findMax' . getVars . fvs


findMax' :: IntSet.IntSet -> Maybe Int
findMax' s
  | IntSet.null s = Nothing
  | otherwise     = Just (IntSet.findMax s)
