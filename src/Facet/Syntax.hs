module Facet.Syntax
( (:::)(..)
, tm
, ty
, (:===:)(..)
, (:=:)(..)
, (:$)(..)
, Telescope(..)
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
import Data.Functor.Classes
import Facet.Semiring
import Facet.Stack

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


data Telescope a b = Telescope [a] b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifoldable Telescope where
  bifoldMap = bifoldMapDefault

instance Bifunctor Telescope where
  bimap = bimapDefault

instance Bitraversable Telescope where
  bitraverse f g (Telescope ctx r) = Telescope <$> traverse f ctx <*> g r


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

instance Eq1 Pl_ where
  liftEq eq (P p1 a1) (P p2 a2) = p1 == p2 && eq a1 a2

instance Ord1 Pl_ where
  liftCompare compare' (P p1 a1) (P p2 a2) = compare p1 p2 <> compare' a1 a2

unPl_ :: (a -> b) -> (a -> b) -> Pl_ a -> b
unPl_ im ex = unPl im ex . pl <*> out

im, ex :: a -> Pl_ a
im = P Im
ex = P Ex
