module Facet.Syntax.Untyped
( Name
, Expr(..)
, Err(..)
, TName
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


type TName = String

class Type ty where
  (-->) :: ty -> ty -> ty
  infixr 2 -->

  (.*) :: ty -> ty -> ty
  infixl 7 .*

  _Unit :: ty

  tglobal :: TName -> ty
