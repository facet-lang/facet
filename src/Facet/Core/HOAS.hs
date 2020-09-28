{-# LANGUAGE TypeOperators #-}
module Facet.Core.HOAS
( Type(..)
) where

import Data.Text (Text)
import Facet.Syntax ((:::)(..))

class Type ty where
  _Type :: ty
  _Unit :: ty

  -- | Universal quantification.
  (>=>) :: (Text ::: ty) -> (ty -> ty) -> ty
  infixr 1 >=>
  (.$) :: ty -> ty -> ty
  infixl 9 .$

  (-->) :: ty -> ty -> ty
  infixr 2 -->
  (.*) :: ty -> ty -> ty
  infixl 7 .*

  -- FIXME: tupling/unit should take a list of types
