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
, bind1
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

import           Data.Bifunctor (first)
import           Data.Coerce
import           Data.Functor.Const
import           Data.Functor.Identity
import qualified Data.IntSet as IntSet
import           Data.Maybe (fromMaybe)
import           Data.Traversable (mapAccumL)
import           Facet.Name
import qualified Facet.Substitution as Subst
import           GHC.Exts

newtype Vars = Vars { getVars :: IntSet.IntSet }
  deriving (Eq, Monoid, Semigroup, Show)

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
  boundVar :: Name a -> t
  bind :: Name a -> t -> t

instance Binding Vars where
  boundVar = Vars . IntSet.singleton . id'
  bind = delete


class Applicative f => Binding1 t f where
  boundVar1 :: (Name a -> t) -> Name a -> f t
  bindN :: Traversable p => (Name a -> t) -> p (Name a) -> FVs -> f t -> f (p (Name a), t)

bind1 :: Binding1 t f => (Name a -> t) -> Name a -> FVs -> f t -> f (Name a, t)
bind1 mk n fvs b = first runIdentity <$> bindN mk (Identity n) fvs b

instance Binding a => Binding1 t (Const a) where
  boundVar1 _ n = Const (boundVar n)
  bindN _ p _ b = Const (foldr (\ n b -> bind n b) (getConst b) p)


substitute :: Subst.Substitution t -> Substitute t a -> a
substitute s m = runSubstitute m s

newtype Substitute t a = Substitute { runSubstitute :: Subst.Substitution t -> a }

instance Functor (Substitute t) where
  fmap f s = Substitute $ \ sub -> f (runSubstitute s sub)

instance Applicative (Substitute t) where
  pure a = Substitute $ \ _ -> a
  f <*> a = Substitute $ \ sub -> runSubstitute f sub (runSubstitute a sub)

instance Scoped1 t => Binding1 t (Substitute t) where
  boundVar1 mk n = Substitute $ \ sub -> fromMaybe (mk n) (Subst.lookup n sub)

  bindN mkBound p fvs b = Substitute $ \ sub ->
    let (sub', p') = renameAccumL (\ i sub n -> let n' = Name (hint n) i in (Subst.insert n (mkBound n') sub, n')) (fvs <> foldMap fvsDefault sub) sub p
        b' = runSubstitute b sub'
    in (p', b')


class Scoped t where
  fvs :: Binding vs => t -> vs

instance Scoped (Name a) where
  fvs = boundVar


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
  boundVar n = FVs $ \ b -> if n `member` b then id else insert n
  bind n v = FVs $ runFVs v . insert n

getFVs :: FVs -> Vars
getFVs v = runFVs v mempty mempty


-- | Construct a fresh name given the provided free variables.
prime :: UName -> FVs -> Name a
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
