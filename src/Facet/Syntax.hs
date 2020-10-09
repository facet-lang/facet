{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Syntax
( (:::)(..)
, tm
, ty
, uncurryAnn
, curryAnn
, (:=)(..)
, splitl
, splitr
) where

import Data.Bifunctor
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


data a := b = a := b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 2 :=

instance Bifunctor (:=) where
  bimap f g (a := b) = f a := g b


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
