{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface
( Name
, Expr(..)
, TName
, Type(..)
, ForAll(..)
, DeclName
, Module(..)
, Decl(..)
, (:::)(..)
) where

import Data.Text (Text)
import Facet.Syntax ((:::)(..))

type Name = Text

class Expr expr where
  global :: Name -> expr

  lam0 :: (expr -> expr) -> expr
  lam :: (Either expr (expr, expr -> expr) -> expr) -> expr
  ($$) :: expr -> expr -> expr
  infixl 9 $$

  unit :: expr
  -- | Tupling.
  (**) :: expr -> expr -> expr
  -- FIXME: tupling/unit should take a list of expressions


class ForAll ty decl | decl -> ty where
  -- | Universal quantification.
  (>=>) :: (TName ::: ty) -> (ty -> decl) -> decl
  infixr 1 >=>


type TName = Text

class ForAll ty ty => Type ty where
  tglobal :: Name -> ty

  (-->) :: ty -> ty -> ty
  infixr 2 -->

  (.$) :: ty -> ty -> ty
  infixl 9 .$

  (.*) :: ty -> ty -> ty
  infixl 7 .*
  -- FIXME: tupling/unit should take a list of types

  _Unit :: ty
  _Type :: ty


type DeclName = Text

-- FIXME: define a core variant of this where declarations are normalized to not contain term bindings in the signature but instead pattern match in the definition
class Decl expr ty decl => Module expr ty decl mod | mod -> decl where
  (.:) :: DeclName -> decl -> mod
  infixr 0 .:

class (Expr expr, ForAll ty decl, Type ty) => Decl expr ty decl | decl -> ty expr where
  (.=) :: ty -> expr -> decl
  infix 1 .=

  (>->) :: ty -> (expr -> decl) -> decl
  infixr 1 >->
