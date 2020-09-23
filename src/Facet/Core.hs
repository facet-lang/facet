module Facet.Core
( Type(..)
, Expr(..)
) where

class Type ty where
  _Type :: ty
  _Unit :: ty

  -- | Universal quantification.
  (>=>) :: ty -> (ty -> ty) -> ty
  infixr 1 >=>
  (-->) :: ty -> ty -> ty
  infixr 2 -->

  (.$) :: ty -> ty -> ty
  infixl 9 .$
  (.*) :: ty -> ty -> ty
  infixl 7 .*
  -- FIXME: tupling/unit should take a list of types


class Expr expr where
  lam0 :: (expr -> expr) -> expr
  ($$) :: expr -> expr -> expr
  infixl 9 $$
