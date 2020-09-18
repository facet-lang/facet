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

  unit :: repr
  -- | Tupling.
  (**) :: repr -> repr -> repr
  -- FIXME: tupling/unit should take a list of expressions


class Err expr where
  err :: expr


type TName = String

class Type ty where
  (-->) :: ty -> ty -> ty
  infixr 2 -->

  (>->) :: ty -> (ty -> ty) -> ty
  infixr 1 >->

  (.*) :: ty -> ty -> ty
  infixl 7 .*
  -- FIXME: tupling/unit should take a list of types

  (.$) :: ty -> ty -> ty
  infixl 9 .$

  _Unit :: ty
  _Type :: ty

  tglobal :: TName -> ty
