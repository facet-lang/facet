{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core
( Type(..)
, Expr(..)
, Module(..)
, Def(..)
) where

import qualified Facet.Core.Pattern as P
import           Facet.Name (E, MName, QName, Name, T)
import           Facet.Syntax ((:::)(..), (:=)(..))

class Type ty where
  tglobal :: QName -> ty
  tbound :: Name T -> ty

  _Type :: ty
  -- FIXME: encode these as datatypes
  _Void :: ty
  _Unit :: ty

  -- | Universal quantification.
  (>=>) :: (Name T ::: ty) -> ty -> ty
  infixr 1 >=>
  (.$) :: ty -> ty -> ty
  infixl 9 .$

  (-->) :: ty -> ty -> ty
  infixr 2 -->
  (.*) :: ty -> ty -> ty
  infixl 7 .*

  -- FIXME: tupling/unit should take a list of types


class Expr expr where
  global :: QName -> expr
  bound :: Name E -> expr
  tlam :: Name T -> expr -> expr
  lam :: P.Pattern (Name E) -> expr -> expr
  ($$) :: expr -> expr -> expr
  infixl 9 $$
  unit :: expr
  (**) :: expr -> expr -> expr


class Def expr ty def | def -> expr ty where
  defTerm :: QName -> (ty := expr) -> def


class Module def mod | mod -> def where
  module' :: MName -> [def] -> mod
