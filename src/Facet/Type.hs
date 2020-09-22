module Facet.Type
( Type(..)
) where

data Type
  = Type
  | Type :-> Type
