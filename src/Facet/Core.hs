{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core
( Type(..)
, Expr(..)
, Module(..)
) where

import Data.Text (Text)
import Facet.Name (Name, QName)
import Facet.Syntax ((:::)(..), (:=)(..))

class Type ty where
  tglobal :: QName -> ty
  tbound :: Name -> ty

  _Type :: ty
  _Unit :: ty

  -- | Universal quantification.
  (==>) :: (Name ::: ty) -> ty -> ty
  infixr 1 ==>
  (.$) :: ty -> ty -> ty
  infixl 9 .$

  (-->) :: ty -> ty -> ty
  infixr 2 -->
  (.*) :: ty -> ty -> ty
  infixl 7 .*

  -- FIXME: tupling/unit should take a list of types


class Expr expr where
  global :: QName -> expr
  bound :: Name -> expr
  tlam :: Name -> expr -> expr
  lam :: Name -> expr -> expr
  ($$) :: expr -> expr -> expr
  infixl 9 $$
  unit :: expr
  (**) :: expr -> expr -> expr


class Module expr ty mod | mod -> expr ty where
  -- FIXME: qualified names
  module' :: Text -> mod -> mod

  -- FIXME: qualified names
  (.:.) :: Text -> (ty := expr) -> mod
  infix 1 .:.
