{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core
( Type(..)
, Expr(..)
, Module(..)
, (>=>)
, tlam'
, lam0'
) where

import Data.Text (Text)
import Facet.Name (Name, Scoped, binder)
import Facet.Syntax ((:::)(..), (:=)(..))

class Type ty where
  -- FIXME: qualified names
  tglobal :: Text -> ty
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

(>=>) :: (Scoped ty, Type ty) => (Text ::: ty) -> (ty -> ty) -> ty
(n ::: t) >=> b = binder tbound ((==>) . (::: t)) n b

infixr 1 >=>

class Expr expr where
  -- FIXME: qualified names
  global :: Text -> expr
  bound :: Name -> expr
  tlam :: Name -> expr -> expr
  lam0 :: Name -> expr -> expr
  ($$) :: expr -> expr -> expr
  infixl 9 $$

tlam' :: (Scoped expr, Expr expr) => Text -> (expr -> expr) -> expr
tlam' = binder bound tlam

lam0' :: (Scoped expr, Expr expr) => Text -> (expr -> expr) -> expr
lam0' = binder bound lam0


class Module expr ty mod | mod -> expr ty where
  -- FIXME: qualified names
  module' :: Text -> mod -> mod

  -- FIXME: qualified names
  (.:.) :: Text -> (expr := ty) -> mod
  infix 1 .:.
