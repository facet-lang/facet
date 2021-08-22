module Facet.Polarized
( Kind(..)
, Type(..)
, XType(..)
, quoteType
, Val(..)
, Elab(..)
) where

import Control.Carrier.Reader
import Facet.Name

data Kind
  = Type
  | Kind :=> Kind
  deriving (Eq, Ord, Show)

infixr 2 :=>

data Type
  = Var Kind Level
  -- negative
  | Up Type
  | Bot
  | Type :-> Type
  | ForAll Kind (Type -> Type)
  -- positive
  | Down Type
  | One
  | Type :>< Type
  | Type :>- Type

infixr 2 :->
infixr 7 :><
infixl 2 :>-


data XType
  = XVar Kind Index
  -- negative
  | XUp XType
  | XBot
  | XType :->: XType
  | XForAll Kind XType
  -- positive
  | XDown XType
  | XOne
  | XType :><: XType
  | XType :>-: XType
  deriving (Eq, Ord, Show)

infixr 2 :->:
infixr 7 :><:
infixl 2 :>-:

quoteType :: Level -> Type -> XType
quoteType d = \case
  Var k d'   -> XVar k (levelToIndex d d')
  Up t       -> XUp (quoteType d t)
  Bot        -> XBot
  a :-> b    -> quoteType d a :->: quoteType d b
  ForAll k b -> XForAll k (quoteType (succ d) (b (Var k d)))
  Down t     -> XDown (quoteType d t)
  One        -> XOne
  a :>< b    -> quoteType d a :><: quoteType d b
  b :>- a    -> quoteType d b :>-: quoteType d a



data Val
  -- negative
  = Lam (Val -> Val)
  | Ret Val
  -- positive
  | Unit
  | Pair Val Val
  | Thunk Val


newtype Elab a = Elab { elab :: [Type] -> Maybe a }
  deriving (Functor)
  deriving (Applicative) via ReaderC [Type] Maybe
