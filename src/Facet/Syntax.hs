{-# LANGUAGE TypeOperators #-}
module Facet.Syntax
( (:::)(..)
, ty
, (.:)
) where

import Facet.Name

data a ::: b = a ::: b
  deriving (Eq, Ord, Show)

infix 5 :::

instance (Scoped a, Scoped b) => Scoped (a ::: b) where
  maxBV (a ::: b) = maxBV a `max` maxBV b

ty :: a ::: b -> b
ty (_ ::: b) = b


(.:) :: Functor m => m a -> b -> m (a ::: b)
tm .: ty = (::: ty) <$> tm

infix 5 .:
