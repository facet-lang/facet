module Facet.Polarized
( NType(..)
, PType(..)
) where

newtype NType
  = Up PType

newtype PType
  = Down NType
