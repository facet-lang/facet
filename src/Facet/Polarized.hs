{-# LANGUAGE GADTs #-}
module Facet.Polarized
( Kind(..)
, NType(..)
, PType(..)
) where

data Kind t where
  NType :: Kind NType
  PType :: Kind PType
  (:=>) :: Kind t1 -> Kind t2 -> Kind (t1 -> t2)

infixr 2 :=>

data NType
  = Up PType
  | PType :-> NType
  | forall t . ForAll (Kind t) (t -> NType)

infixr 2 :->

newtype PType
  = Down NType
