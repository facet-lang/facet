module Facet.Surface.Type.Expr
( Type(..)
, Interface(..)
) where

import Facet.Kind
import Facet.Name
import Facet.Snoc
import Facet.Syntax

-- Types

data Type
  = TVar QName
  | TString
  | TForAll Name Kind (Ann Type)
  | TArrow (Maybe Name) (Ann Type) (Ann Type)
  | TComp [Ann (Interface (Ann Type))] (Ann Type)
  | TApp (Ann Type) (Ann Type)
  deriving (Eq, Show)


data Interface a = Interface QName (Snoc a)
  deriving (Eq, Show)
