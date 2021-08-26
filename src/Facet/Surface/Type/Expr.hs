module Facet.Surface.Type.Expr
( Kind(..)
, Type(..)
, Interface(..)
, Mul(..)
) where

import Facet.Name
import Facet.Snoc
import Facet.Syntax

-- Types

data Kind
  = KType
  | KInterface
  | KArrow (Maybe Name) (Ann Comment Kind) (Ann Comment Kind)
  deriving (Eq, Show)

data Type
  = TVar QName
  | TString
  | TForAll Name (Ann Comment Kind) (Ann Comment Type)
  | TArrow (Maybe Name) (Maybe Mul) (Ann Comment Type) (Ann Comment Type)
  | TComp [Ann Comment (Interface (Ann Comment Type))] (Ann Comment Type)
  | TApp (Ann Comment Type) (Ann Comment Type)
  deriving (Eq, Show)


data Interface a = Interface (Ann Comment QName) (Snoc a)
  deriving (Eq, Show)


data Mul = Zero | One
  deriving (Bounded, Enum, Eq, Ord, Show)
