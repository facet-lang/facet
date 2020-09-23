module Facet.Type
( Type(..)
) where

import qualified Facet.Core as C

data Type
  = Type
  | Unit
  | Type :* Type
  | Type :$ Type
  | Type :-> Type
  | ForAll Type (Type -> Type)

infixl 7 :*
infixr 0 :->
infixl 9 :$

instance C.Type Type where
  _Type = Type
  _Unit = Unit
  (.*) = (:*)
  (-->) = (:->)
  (>=>) = ForAll
  (.$) = (:$)
