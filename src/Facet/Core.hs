module Facet.Core
( Type(..)
) where

class Type ty where
  _Type :: ty
  _Unit :: ty

  -- | Universal quantification.
  (>=>) :: ty -> (ty -> decl) -> decl
  infixr 1 >=>
  (-->) :: ty -> ty -> ty
  infixr 2 -->

  (.*) :: ty -> ty -> ty
  infixl 7 .*
  -- FIXME: tupling/unit should take a list of types
