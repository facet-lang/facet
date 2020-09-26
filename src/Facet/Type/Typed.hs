{-# LANGUAGE GADTs #-}
module Facet.Type.Typed
( Type(..)
, (-->)
, (.+)
, (.*)
) where

import qualified Data.Kind as K

data Type k t where
  Var :: Int -> Type k t
  Type :: Type K.Type K.Type
  Unit :: Type K.Type ()
  ForAll :: Type K.Type ka -> (Type ka ta -> Type kb tb) -> Type (ka -> kb) (ta -> tb)
  (:$) :: Type (ka -> kb) (ta -> tb) -> Type ka ta -> Type kb tb
  Arr :: Type (K.Type -> K.Type -> K.Type) (ta -> tb -> (ta -> tb))
  Sum :: Type (K.Type -> K.Type -> K.Type) (ta -> tb -> Either ta tb)
  Prd :: Type (K.Type -> K.Type -> K.Type) (ta -> tb -> (ta, tb))

infixl 9 :$

(-->) :: Type K.Type ta -> Type K.Type tb -> Type K.Type (ta -> tb)
a --> b = Arr :$ a :$ b

infixr 0 -->

(.+) :: Type K.Type ta -> Type K.Type tb -> Type K.Type (Either ta tb)
a .+ b = Sum :$ a :$ b

infixl 6 .+

(.*) :: Type K.Type ta -> Type K.Type tb -> Type K.Type (ta, tb)
a .* b = Prd :$ a :$ b

infixl 7 .*
