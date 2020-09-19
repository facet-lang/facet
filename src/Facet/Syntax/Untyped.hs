{-# LANGUAGE FunctionalDependencies #-}
module Facet.Syntax.Untyped
( App(..)
, Name
, Expr(..)
, Err(..)
, TName
, Type(..)
, ForAll(..)
, DeclName
, Module(..)
, Decl(..)
) where

class App expr where
  ($$) :: expr -> expr -> expr
  infixl 9 $$


type Name = String

class App repr => Expr repr where
  lam0 :: (repr -> repr) -> repr
  lam :: (Either repr (repr, repr -> repr) -> repr) -> repr

  global :: Name -> repr

  unit :: repr
  -- | Tupling.
  (**) :: repr -> repr -> repr
  -- FIXME: tupling/unit should take a list of expressions


class Err expr where
  err :: expr


class ForAll ty decl | decl -> ty where
  -- | Universal quantification.
  (>=>) :: ty -> (ty -> decl) -> decl
  infixr 1 >=>


type TName = String

class ForAll ty ty => Type ty where
  (-->) :: ty -> ty -> ty
  infixr 2 -->

  (.*) :: ty -> ty -> ty
  infixl 7 .*
  -- FIXME: tupling/unit should take a list of types

  (.$) :: ty -> ty -> ty
  infixl 9 .$

  _Unit :: ty
  _Type :: ty

  tglobal :: TName -> ty


type DeclName = String

class Decl expr ty decl => Module expr ty decl mod | mod -> decl where
  (.:) :: DeclName -> decl -> mod
  infixr 0 .:

class (Expr expr, ForAll ty decl, Type ty) => Decl expr ty decl | decl -> ty expr where
  (.=) :: ty -> expr -> decl
  infix 1 .=

  (>->) :: ty -> (expr -> decl) -> decl
  infixr 1 >->
