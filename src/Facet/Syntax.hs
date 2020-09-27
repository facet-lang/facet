{-# LANGUAGE TypeOperators #-}
module Facet.Syntax
( (:::)(..)
, (.:)
) where

data a ::: b = a ::: b
  deriving (Eq, Ord, Show)

infix 5 :::


(.:) :: Functor m => m a -> b -> m (a ::: b)
tm .: ty = (::: ty) <$> tm

infix 5 .:
