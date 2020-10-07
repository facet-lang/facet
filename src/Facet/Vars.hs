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
, renameAccumL
) where

import           Data.Coerce
import qualified Data.IntSet as IntSet
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           GHC.Exts
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
  FVs v1 <> FVs v2 = FVs $ oneShot $ \ b -> oneShot $ \ f -> v1 b (v2 b f)

instance Monoid FVs where
  mempty = FVs (const id)

instance Binding FVs where
  singleton n = FVs $ \ b -> if n `member` b then id else insert n
  bind n v = FVs $ runFVs v . insert n

getFVs :: FVs -> Vars
getFVs v = runFVs v mempty mempty


-- | Construct a fresh name given the provided free variables.
prime :: Text -> FVs -> Name
prime n = Name n . freshIdForFVs

renameAccumL :: Traversable t => (Int -> a -> b -> (a, c)) -> FVs -> a -> t b -> (a, t c)
renameAccumL f fvs a t = let ((_, a'), t') = mapAccumL step (base, a) t in (a', t')
  where
  step (i, a) b = let (a', c) = f i a b in ((i + 1, a'), c)
  base = freshIdForFVs fvs


freshIdForFVs :: FVs -> Int
freshIdForFVs = maybe 0 (+ 1) . findMax' . getVars . getFVs

findMax' :: IntSet.IntSet -> Maybe Int
findMax' s
  | IntSet.null s = Nothing
  | otherwise     = Just (IntSet.findMax s)
