module Facet.Sequent.Type
( Type(..)
) where

data Type
  = String
  | One
  | Type :+ Type
  | Type :* Type
  | Type :-> Type
  deriving (Eq, Ord, Show)

infixl 6 :+
infixl 7 :*
infixr 1 :->
