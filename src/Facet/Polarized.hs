{-# LANGUAGE GADTs #-}
module Facet.Polarized
( Kind(..)
, NType(..)
, PType(..)
, NVal(..)
, PVal(..)
, Elab(..)
) where

import Control.Carrier.Reader
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


data NVal
  = Lam (PVal -> NVal)
  | Ret PVal

data PVal
  = Unit
  | Pair PVal PVal
  | Thunk NVal


newtype Elab a = Elab { elab :: [(String, PType)] -> [(String, NType)] -> Maybe a }
  deriving (Functor)
  deriving (Applicative) via ReaderC [(String, PType)] (ReaderC [(String, NType)] Maybe)
