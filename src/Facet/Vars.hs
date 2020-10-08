{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Vars
( Vars(..)
, insert
, delete
, difference
, member
, Binding(..)
, Binding1(..)
, substitute
, Substitute(..)
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


class Applicative f => Binding1 t f where
  bound1 :: (Name a -> t) -> Name a -> f t
  bind1 :: (Name a -> t) -> Name a -> t -> f (Name a, t)

instance (Scoped1 t, Binding a) => Binding1 t (Const a) where
  bound1 _ n = Const (bound n)
  bind1 _ n b = Const (bind n (getConst (fvs1 b)))


substitute :: Subst.Substitution t -> Substitute t a -> a
substitute s m = runSubstitute m s

newtype Substitute t a = Substitute { runSubstitute :: Subst.Substitution t -> a }

instance Functor (Substitute t) where
  fmap f s = Substitute $ \ sub -> f (runSubstitute s sub)

instance Applicative (Substitute t) where
  pure a = Substitute $ \ _ -> a
  f <*> a = Substitute $ \ sub -> runSubstitute f sub (runSubstitute a sub)

instance Scoped1 t => Binding1 t (Substitute t) where
  bound1 mk n = Substitute $ \ sub -> fromMaybe (mk n) (Subst.lookup n sub)

  bind1 mkBound n b = Substitute $ \ sub ->
    let n' = prime (hint n) (fvsDefault b <> foldMap fvsDefault sub)
        b' = runSubstitute (fvs1 b) (Subst.insert n (mkBound n') sub)
    in (n', b')


class Scoped t where
  fvs :: Binding vs => t -> vs

instance Scoped (Name a) where
  fvs = bound


class Scoped1 t where
  fvs1 :: Binding1 t vs => t -> vs t

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
