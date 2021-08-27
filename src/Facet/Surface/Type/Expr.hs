module Facet.Surface.Type.Expr
( Type(..)
, Interface(..)
, Mul(..)
) where

import Facet.Kind
import Facet.Name
import Facet.Snoc
import Facet.Syntax

-- Types

data Type
  = TVar QName
  | TString
  | TForAll Name Kind (Ann Comment Type)
  | TArrow (Maybe Name) (Maybe Mul) (Ann Comment Type) (Ann Comment Type)
  | TComp [Ann Comment (Interface (Ann Comment Type))] (Ann Comment Type)
  | TApp (Ann Comment Type) (Ann Comment Type)
  deriving (Eq, Show)


data Interface a = Interface QName (Snoc a)
  deriving (Eq, Show)


data Mul = Zero | One
  deriving (Bounded, Enum, Eq, Ord, Show)
