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
, getFVs
, prime
, renameWith
) where

import           Control.Carrier.Fresh.Church
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


-- https://www.haskell.org/ghc/blog/20190728-free-variable-traversals.html 🎩 bgamari
class Monoid t => Binding t where
  singleton :: Name -> t
  bind :: Name -> t -> t

instance Binding Vars where
  singleton = Vars . IntSet.singleton . id'
  bind = delete


class Scoped t where
  fvs :: Binding vs => t -> vs

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

getFVs :: FVs -> Vars
getFVs v = runFVs v mempty mempty


-- | Construct a fresh name given the provided free variables.
prime :: Text -> FVs -> Name
prime n = Name n . maybe 0 (+ 1) . findMax' . getVars . getFVs

renameWith :: Traversable t => (Int -> a -> b) -> t a -> FVs -> t b
renameWith f ts fvs = run (evalFresh base (traverse (\ a -> f <$> fresh <*> pure a) ts))
  where
  base = maybe 0 (+ 1) (findMax' (getVars (getFVs fvs)))


findMax' :: IntSet.IntSet -> Maybe Int
findMax' s
  | IntSet.null s = Nothing
  | otherwise     = Just (IntSet.findMax s)
