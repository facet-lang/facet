module Facet.Type
( Type(..)
) where

class Type ty where
  (-->) :: ty -> ty
  infixr 2 -->
