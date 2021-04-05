module Facet.Type.Expr
( Type(..)
) where

import Facet.Interface
import Facet.Kind
import Facet.Name
import Facet.Syntax
import Facet.Usage

data Type
  = TString
  | TVar (Var (Either Meta (LName Index)))
  | TForAll Name Kind Type
  | TArrow (Maybe Name) Quantity Type Type
  | TComp (Signature Type) Type
  | TApp Type Type
  deriving (Eq, Ord, Show)
