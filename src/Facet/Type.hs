module Facet.Type
( Type(..)
) where

import qualified Facet.Core as C

data Type a
  = Type
  | Unit
  | Type a :* Type a
  | Type a :$ Type a
  | Type a :-> Type a
  | ForAll (Type a) (Type a -> Type a)

infixl 7 :*
infixr 0 :->
infixl 9 :$

instance C.Type (Type a) where
  _Type = Type
  _Unit = Unit
  (.*) = (:*)
  (-->) = (:->)
  (>=>) = ForAll
  (.$) = (:$)
