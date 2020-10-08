{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Vars
( Vars(..)
, insert
, delete
, difference
, member
, Binding(..)
, Binding1(..)
, Rename(..)
, Substitute(..)
, Scoped(..)
, Scoped1(..)
, fvsDefault
, Substitution(..)
, FVs(..)
, getFVs
, prime
, renameAccumL
) where

import           Data.Coerce
import           Data.Functor.Const
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Facet.Name
import           GHC.Exts

newtype Vars = Vars { getVars :: IntSet.IntSet }
  deriving (Monoid, Semigroup, Show)

insert :: Name a -> Vars -> Vars
insert = coerce (IntSet.insert . id')

delete :: Name a -> Vars -> Vars
delete = coerce (IntSet.delete . id')

difference :: Vars -> Vars -> Vars
difference = coerce IntSet.difference

member :: Name a -> Vars -> Bool
member = coerce (IntSet.member . id')


-- https://www.haskell.org/ghc/blog/20190728-free-variable-traversals.html 🎩 bgamari
class Monoid t => Binding t where
  bound :: Name a -> t
  bind :: Name a -> t -> t

instance Binding Vars where
  bound = Vars . IntSet.singleton . id'
  bind = delete


class Applicative t => Binding1 t where
  bound1 :: Name a -> t (Name a)
  bind1 :: Name a -> t b -> t b

instance Binding a => Binding1 (Const a) where
  bound1 n = Const (bound n)
  bind1 n (Const b) = Const (bind n b)


newtype Rename a = Rename { runRename :: forall x . Name x -> Name x -> a }

instance Functor Rename where
  fmap f r = Rename $ \ x y -> f (runRename r x y)

instance Applicative Rename where
  pure a = Rename $ \ _ _ -> a
  f <*> a = Rename $ \ x y -> runRename f x y (runRename a x y)

instance Binding1 Rename where
  bound1 z = Rename $ \ x y -> if z == coerce x then coerce y else z
  -- FIXME: this is inefficient; it has to traverse the entirety of b even if it’s not going to do anything to it
  bind1 z b = Rename $ \ x y -> if z == coerce x then runRename b z z else runRename b x y


newtype Substitute a = Substitute { runSubstitute :: forall x t . Scoped1 t => Name x -> t -> a }

instance Functor Substitute where
  fmap f s = Substitute $ \ x e -> f (runSubstitute s x e)

instance Applicative Substitute where
  pure a = Substitute $ \ _ _ -> a
  f <*> a = Substitute $ \ x e -> runSubstitute f x e (runSubstitute a x e)


class Scoped t where
  fvs :: Binding vs => t -> vs

instance Scoped (Name a) where
  fvs = bound


class Scoped1 t where
  fvs1 :: Binding1 vs => t -> vs t

fvsDefault :: (Scoped1 t, Binding vs) => t -> vs
fvsDefault = getConst . fvs1


newtype Substitution a = Substitution { getSubstitution :: IntMap.IntMap a }


newtype FVs = FVs { runFVs :: Vars -> Vars -> Vars }

instance Semigroup FVs where
  FVs v1 <> FVs v2 = FVs $ oneShot $ \ b -> oneShot $ \ f -> v1 b (v2 b f)

instance Monoid FVs where
  mempty = FVs (const id)

instance Binding FVs where
  bound n = FVs $ \ b -> if n `member` b then id else insert n
  bind n v = FVs $ runFVs v . insert n

getFVs :: FVs -> Vars
getFVs v = runFVs v mempty mempty


-- | Construct a fresh name given the provided free variables.
prime :: Text -> FVs -> Name a
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
