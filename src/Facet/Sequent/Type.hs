module Facet.Sequent.Type
( Type(..)
) where

import Facet.Kind (Kind)
import Facet.Name (Name)
import Facet.Usage (Quantity)

data Type
  = String
  | One
  | Type :+ Type
  | Type :* Type
  | ForAll Name Kind (Type -> Type)
  | Arrow (Maybe Name) Quantity Type Type

infixl 6 :+
infixl 7 :*
