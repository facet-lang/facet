module Facet.Sequent.Type
( Type(..)
) where

import Facet.Name (Name)
import Facet.Usage (Quantity)

data Type
  = String
  | One
  | Type :+ Type
  | Type :* Type
  | Arrow (Maybe Name) Quantity Type Type
  deriving (Eq, Ord, Show)

infixl 6 :+
infixl 7 :*
