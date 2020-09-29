{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Syntax
( (:::)(..)
, tm
, ty
, uncurryAnn
, curryAnn
, (.:)
, Stack(..)
) where

import Data.Bifunctor
import Facet.Name

data a ::: b = a ::: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 5 :::

instance Bifunctor (:::) where
  bimap f g (a ::: b) = f a ::: g b

instance (Scoped a, Scoped b) => Scoped (a ::: b) where
  maxBV (a ::: b) = maxBV a <> maxBV b

tm :: a ::: b -> a
tm (a ::: _) = a

ty :: a ::: b -> b
ty (_ ::: b) = b


uncurryAnn :: (a -> b -> c) -> ((a ::: b) -> c)
uncurryAnn f ~(a ::: b) = f a b

curryAnn :: ((a ::: b) -> c) -> (a -> b -> c)
curryAnn f a b = f (a ::: b)


(.:) :: Functor m => m a -> b -> m (a ::: b)
tm .: ty = (::: ty) <$> tm

infixr 5 .:


data Stack a
  = Nil
  | Stack a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 5 :>
