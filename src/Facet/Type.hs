module Facet.Type
( Type(..)
) where

data Type
  = Type
  | Unit
  | Type :-> Type
  | ForAll Type (Type -> Type)
