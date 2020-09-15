module Facet.Type
( Type(..)
) where

class Type ty where
  (-->) :: ty expr a -> ty expr b -> ty expr (expr a -> expr b)
  infixr 2 -->

  _Unit :: ty expr ()
