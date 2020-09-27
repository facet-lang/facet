{-# LANGUAGE TypeOperators #-}
module Facet.Syntax
( (:::)(..)
, (.:)
) where

import Facet.Name

data a ::: b = a ::: b
  deriving (Eq, Ord, Show)

infix 5 :::

instance (Scoped a, Scoped b) => Scoped (a ::: b) where
  maxBV (a ::: b) = maxBV a `max` maxBV b


(.:) :: Functor m => m a -> b -> m (a ::: b)
tm .: ty = (::: ty) <$> tm

infix 5 .:
