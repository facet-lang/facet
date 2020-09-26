{-# LANGUAGE GADTs #-}
module Facet.Type.Typed
( Type(..)
) where

import qualified Data.Kind as K

data Type t k where
  Type :: Type K.Type K.Type
  Unit :: Type () K.Type
  (:->) :: Type ta K.Type -> Type tb K.Type -> Type (ta -> tb) K.Type
  (:$) :: Type (ta -> tb) (ka -> kb) -> Type ta ka -> Type tb kb
  (:*) :: Type a K.Type -> Type b K.Type -> Type (a, b) K.Type
  ForAll :: Type a K.Type -> (Type ta a -> Type tb b) -> Type (ta -> tb) (a -> b)

infixl 7 :*
infixr 0 :->
infixl 9 :$
