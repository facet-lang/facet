module Facet.Polarized
( Kind(..)
, NType(..)
, PType(..)
) where

data Kind
  = Type

data NType
  = Up PType
  | PType :-> NType

infixr 2 :->

newtype PType
  = Down NType
