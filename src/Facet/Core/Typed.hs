module Facet.Core.Typed
( Type(..)
, Interpret(..)
) where

import qualified Data.Kind as K

class Type ty where
  _Type :: ty K.Type
  _Unit :: ty K.Type

  -- | Universal quantification.
  (>=>) :: ty K.Type -> (ty k1 -> ty k2) -> ty (k1 -> k2)
  infixr 1 >=>
  (.$) :: ty (k1 -> k2) -> ty k1 -> ty k2
  infixl 9 .$

  (-->) :: ty K.Type -> ty K.Type -> ty K.Type
  infixr 2 -->
  (.*) :: ty K.Type -> ty K.Type -> ty K.Type
  infixl 7 .*

  -- FIXME: tupling/unit should take a list of types


class Interpret f where
  interpret :: Type ty => f ty a -> ty a
