module Facet.Syntax.Untyped
( Name
, Expr(..)
, Err(..)
, Type(..)
) where

type Name = String

class Expr repr where
  lam0 :: (repr -> repr) -> repr
  lam :: (Either repr (repr, repr -> repr) -> repr) -> repr
  ($$) :: repr -> repr -> repr
  infixl 9 $$

  global :: Name -> repr

class Err expr where
  err :: expr

class Type ty where
  (-->) :: ty -> ty -> ty
  infixr 2 -->

  (.*) :: ty -> ty -> ty
  infixl 7 .*

  _Unit :: ty
