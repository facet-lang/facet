{-# LANGUAGE TypeOperators #-}
module Facet.Core
( Type(..)
, Expr(..)
, Interpret(..)
) where

import Facet.Name (Name)
import Facet.Syntax ((:::))

class Type ty where
  bound :: Name -> ty

  _Type :: ty
  _Unit :: ty

  -- | Universal quantification.
  (>=>) :: (Name ::: ty) -> ty -> ty
  infixr 1 >=>
  (.$) :: ty -> ty -> ty
  infixl 9 .$

  (-->) :: ty -> ty -> ty
  infixr 2 -->
  (.*) :: ty -> ty -> ty
  infixl 7 .*

  -- FIXME: tupling/unit should take a list of types


class Expr expr where
  lam0 :: (expr -> expr) -> expr
  ($$) :: expr -> expr -> expr
  infixl 9 $$


class Interpret f where
  interpret :: Type ty => f ty -> ty
