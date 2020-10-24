module Facet.Syntax
( (:::)(..)
, tm
, ty
, uncurryAnn
, curryAnn
, (:===:)(..)
, (:=:)(..)
, (:|-:)(..)
, Neutral(..)
, splitl
, splitr
, Pl(..)
, unPl
, Pl_(..)
, unPl_
, im
, ex
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Facet.Semiring
import Facet.Stack

data a ::: b = a ::: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 2 :::

instance Bifunctor (:::) where
  bimap f g (a ::: b) = f a ::: g b

tm :: a ::: b -> a
tm (a ::: _) = a

ty :: a ::: b -> b
ty (_ ::: b) = b


uncurryAnn :: (a -> b -> c) -> ((a ::: b) -> c)
uncurryAnn f ~(a ::: b) = f a b

curryAnn :: ((a ::: b) -> c) -> (a -> b -> c)
curryAnn f a b = f (a ::: b)


data a :===: b = a :===: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 0 :===:

instance Bifoldable (:===:) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (:===:) where
  bimap = bimapDefault

instance Bitraversable (:===:) where
  bitraverse f g (a :===: b) = (:===:) <$> f a <*> g b


data a :=: b = a :=: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 2 :=:

instance Bifunctor (:=:) where
  bimap f g (a :=: b) = f a :=: g b


data a :|-: b = a :|-: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 0 :|-:

instance Bifunctor (:|-:) where
  bimap f g (a :|-: b) = f a :|-: g b


data Neutral a b = (:$)
  { head  :: a
  , spine :: Stack b
  }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 9 :$

instance Bifoldable Neutral where
  bifoldMap = bifoldMapDefault

instance Bifunctor Neutral where
  bimap = bimapDefault

instance Bitraversable Neutral where
  bitraverse f g (h :$ sp) = (:$) <$> f h <*> traverse g sp


splitl :: (t -> Maybe (t, a)) -> t -> (t, Stack a)
splitl un = go id
  where
  go as t = case un t of
    Just (t', a) -> go (as . (:> a)) t'
    Nothing      -> (t, as Nil)

splitr :: (t -> Maybe (a, t)) -> t -> ([a], t)
splitr un = go id
  where
  go as t = case un t of
    Just (a, t') -> go (as . (a:)) t'
    Nothing      -> (as [], t)


-- | Im/explicit.
data Pl
  = Im
  | Ex
  deriving (Bounded, Enum, Eq, Ord, Show)

instance Semigroup Pl where
  Im <> Im = Im
  _  <> _  = Ex

instance Monoid Pl where
  mempty = Im

instance Semiring Pl where
  Ex >< Ex = Ex
  _  >< _  = Im

instance Unital Pl where
  one = Ex

unPl :: a -> a -> Pl -> a
unPl im ex = \case
  Im -> im
  Ex -> ex


data Pl_ a = P
  { pl  :: Pl
  , out :: a
  }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unPl_ :: (a -> b) -> (a -> b) -> Pl_ a -> b
unPl_ im ex = unPl im ex . pl <*> out

im, ex :: a -> Pl_ a
im = P Im
ex = P Ex
