{-# LANGUAGE GADTs #-}
module Facet.Polarized
( Kind(..)
, Type(..)
, XType(..)
, Val(..)
, Elab(..)
) where

import Control.Carrier.Reader
data Kind t where
  Type :: Kind Type
  (:=>) :: Kind t1 -> Kind t2 -> Kind (t1 -> t2)

infixr 2 :=>

data Type
  -- negative
  = Up Type
  | NVar String
  | Bot
  | Type :-> Type
  | forall t . ForAll (Kind t) (t -> Type)
  -- positive
  | Down Type
  | PVar String
  | One
  | Type :>< Type
  | Type :>- Type

infixr 2 :->
infixr 7 :><
infixl 2 :>-


data XType
  -- negative
  = XUp XType
  | XNVar String
  | XBot
  | XType :->: XType
  -- positive
  | XDown XType
  | XPVar String
  | XOne
  | XType :><: XType
  | XType :>-: XType
  deriving (Eq, Ord, Show)

infixr 2 :->:
infixr 7 :><:
infixl 2 :>-:


data Val
  -- negative
  = Lam (Val -> Val)
  | Ret Val
  -- positive
  | Unit
  | Pair Val Val
  | Thunk Val


newtype Elab a = Elab { elab :: [(String, Type)] -> Maybe a }
  deriving (Functor)
  deriving (Applicative) via ReaderC [(String, Type)] Maybe
