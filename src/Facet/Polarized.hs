module Facet.Polarized
( NType(..)
, PType(..)
) where

data NType
  = Up PType
  | PType :-> NType

infixr 2 :->

newtype PType
  = Down NType
