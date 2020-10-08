{-# LANGUAGE TypeOperators #-}
module Facet.Core
( Type(..)
) where

import Facet.Name (Name, QName, T)
import Facet.Syntax ((:::)(..))

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
