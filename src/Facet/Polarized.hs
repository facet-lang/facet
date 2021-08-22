{-# LANGUAGE GADTs #-}
module Facet.Polarized
( Kind(..)
, NType(..)
, PType(..)
) where

data Kind where
  NType :: Kind
  PType :: Kind
  (:=>) :: Kind -> Kind -> Kind

infixr 2 :=>

data NType
  = Up PType
  | PType :-> NType
  | ForAll Kind (Either NType PType -> NType)

infixr 2 :->

newtype PType
  = Down NType
