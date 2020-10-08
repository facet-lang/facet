{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Vars
( Vars(..)
, insert
, delete
, difference
, member
, Binding(..)
, Binding1(..)
, Substitute(..)
, boundS
, Scoped(..)
, Scoped1(..)
, fvsDefault
, FVs(..)
, getFVs
, prime
, renameAccumL
) where

import           Data.Coerce
import           Data.Functor.Const
import qualified Data.IntSet as IntSet
import           Data.Maybe (fromMaybe)
import           Data.Text (Text)
import           Data.Traversable (mapAccumL)
import           Facet.Name
import qualified Facet.Substitution as Subst
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


newtype Substitute t a = Substitute { runSubstitute :: Subst.Substitution t -> a }

instance Functor (Substitute t) where
  fmap f s = Substitute $ \ sub -> f (runSubstitute s sub)

instance Applicative (Substitute t) where
  pure a = Substitute $ \ _ -> a
  f <*> a = Substitute $ \ sub -> runSubstitute f sub (runSubstitute a sub)


boundS :: Name a -> (Name a -> t) -> Substitute t t
boundS n mk = Substitute $ \ sub -> fromMaybe (mk n) (Subst.lookup n sub)


class Scoped t where
  fvs :: Binding vs => t -> vs

instance Scoped (Name a) where
  fvs = bound


class Scoped1 t where
  fvs1 :: Binding1 vs => t -> vs t

fvsDefault :: (Scoped1 t, Binding vs) => t -> vs
fvsDefault = getConst . fvs1


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
