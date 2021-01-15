module Facet.Syntax
( Type
, Term
, (:::)(..)
, tm
, ty
, (:===:)(..)
, (:=:)(..)
, (:$)(..)
, splitl
, splitr
, Icit(..)
, unPl
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor.Classes
import Facet.Semiring
import Facet.Stack

-- | An explicit sort index for type- (and kind-, etc.) level expressions and values.
data Type

-- | An explicit sort index for term-level expressions and values.
data Term


data a ::: b = a ::: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 2 :::

instance Bifoldable (:::) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (:::) where
  bimap = bimapDefault

instance Bitraversable (:::) where
  bitraverse f g (a ::: b) = (:::) <$> f a <*> g b

instance Eq a => Eq1 ((:::) a) where
  liftEq = liftEq2 (==)

instance Ord a => Ord1 ((:::) a) where
  liftCompare = liftCompare2 compare

instance Eq2 (:::) where
  liftEq2 eqA eqB (a1 ::: b1) (a2 ::: b2) = eqA a1 a2 && eqB b1 b2

instance Ord2 (:::) where
  liftCompare2 compareA compareB (a1 ::: b1) (a2 ::: b2) = compareA a1 a2 <> compareB b1 b2

tm :: a ::: b -> a
tm (a ::: _) = a

ty :: a ::: b -> b
ty (_ ::: b) = b


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

instance Bifoldable (:=:) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (:=:) where
  bimap = bimapDefault

instance Bitraversable (:=:) where
  bitraverse f g (a :=: b) = (:=:) <$> f a <*> g b


data a :$ b = a :$ Stack b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 9 :$

instance Bifoldable (:$) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (:$) where
  bimap = bimapDefault

instance Bitraversable (:$) where
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
data Icit
  = Im
  | Ex
  deriving (Bounded, Enum, Eq, Ord, Show)

instance Semigroup Icit where
  Im <> Im = Im
  _  <> _  = Ex

instance Monoid Icit where
  mempty = Im

instance Semiring Icit where
  Ex >< Ex = Ex
  _  >< _  = Im

instance Unital Icit where
  one = Ex

unPl :: a -> a -> Icit -> a
unPl im ex = \case
  Im -> im
  Ex -> ex
