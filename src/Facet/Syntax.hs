{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Syntax
( (:::)(..)
, tm
, ty
, uncurryAnn
, curryAnn
, (:=)(..)
, Stack(..)
, unprefixl
, unprefixr
) where

import Data.Bifunctor
import Facet.Name

data a ::: b = a ::: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 2 :::

instance Bifunctor (:::) where
  bimap f g (a ::: b) = f a ::: g b

instance (Scoped a, Scoped b) => Scoped (a ::: b) where
  fvs (a ::: b) = fvs a <> fvs b

tm :: a ::: b -> a
tm (a ::: _) = a

ty :: a ::: b -> b
ty (_ ::: b) = b


uncurryAnn :: (a -> b -> c) -> ((a ::: b) -> c)
uncurryAnn f ~(a ::: b) = f a b

curryAnn :: ((a ::: b) -> c) -> (a -> b -> c)
curryAnn f a b = f (a ::: b)


data a := b = a := b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 2 :=

instance Bifunctor (:=) where
  bimap f g (a := b) = f a := g b


data Stack a
  = Nil
  | Stack a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 5 :>

unprefixl :: (t -> Maybe (t, a)) -> t -> (t, Stack a)
unprefixl un = go id
  where
  go as t = case un t of
    Just (t', a) -> go ((:> a) . as) t'
    Nothing      -> (t, as Nil)

unprefixr :: (t -> Maybe (a, t)) -> t -> ([a], t)
unprefixr un = go id
  where
  go as t = case un t of
    Just (a, t') -> go (as . (a:)) t'
    Nothing      -> (as [], t)
