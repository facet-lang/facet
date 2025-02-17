module Facet.Sequent.Type
( Type(..)
) where

import Facet.Kind (Kind)
import Facet.Name (Name)

data Type
  = String
  | Type :+ Type
  | Type :* Type
  | ForAll Name Kind (Type -> Type)
  | Arrow (Maybe Name) Type Type

infixl 6 :+
infixl 7 :*
