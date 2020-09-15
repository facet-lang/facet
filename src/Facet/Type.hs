module Facet.Type
( Type(..)
) where

class Type ty where
  (-->) :: ty expr a -> ty expr b -> ty expr (expr a -> expr b)
  infixr 2 -->

  (.*) :: ty expr a -> ty expr b -> ty expr (a, b)
  infixl 7 .*

  _Unit :: ty expr ()
