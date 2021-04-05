module Facet.Core.Type.Expr
( TExpr(..)
) where

import Facet.Core.Interface
import Facet.Core.Kind
import Facet.Name
import Facet.Syntax
import Facet.Usage

data TExpr
  = TString
  | TVar (Var (Either Meta (LName Index)))
  | TForAll Name Kind TExpr
  | TArrow (Maybe Name) Quantity TExpr TExpr
  | TComp (Signature TExpr) TExpr
  | TApp TExpr TExpr
  deriving (Eq, Ord, Show)
