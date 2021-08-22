{-# LANGUAGE GADTs #-}
module Facet.Polarized
( Kind(..)
, NType(..)
, PType(..)
, NVal(..)
, PVal(..)
, Elab(..)
) where

data Kind t where
  NType :: Kind NType
  PType :: Kind PType
  (:=>) :: Kind t1 -> Kind t2 -> Kind (t1 -> t2)

infixr 2 :=>

data NType
  = Up PType
  | NVar String
  | Bot
  | PType :-> NType
  | forall t . ForAll (Kind t) (t -> NType)

infixr 2 :->

data PType
  = Down NType
  | PVar String
  | One
  | PType :>< PType
  | NType :>- PType

infixr 7 :><
infixl 2 :>-


data NVal t where
  Lam :: (PVal a -> NVal b) -> NVal (a -> b)

data PVal t where
  Unit :: PVal ()
  Pair :: PVal a -> PVal b -> PVal (a, b)


newtype Elab a = Elab { elab :: [(String, PType)] -> [(String, NType)] -> Maybe a }
