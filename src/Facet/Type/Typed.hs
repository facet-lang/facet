{-# LANGUAGE GADTs #-}
module Facet.Type.Typed
( Type(..)
) where

import qualified Data.Kind as K

data Type k t where
  Type :: Type K.Type K.Type
  Unit :: Type K.Type ()
  (:->) :: Type K.Type ta -> Type K.Type tb -> Type K.Type (ta -> tb)
  (:$) :: Type (ka -> kb) (ta -> tb) -> Type ka ta -> Type kb tb
  (:*) :: Type K.Type ta -> Type K.Type tb -> Type K.Type (ta, tb)
  ForAll :: Type K.Type ka -> (Type ka ta -> Type kb tb) -> Type (ka -> kb) (ta -> tb)

infixl 7 :*
infixr 0 :->
infixl 9 :$
