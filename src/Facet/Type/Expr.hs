module Facet.Type.Expr
( Type(..)
) where

import Facet.Interface
import Facet.Kind
import Facet.Name
import Facet.Syntax
import Facet.Usage

data Type
  = String
  | Var (Var (Either Meta (LName Index)))
  | ForAll Name Kind Type
  | Arrow (Maybe Name) Quantity Type Type
  | Comp (Signature Type) Type
  | App Type Type
  deriving (Eq, Ord, Show)
