module Facet.Core.Term
( -- * Term expressions
  Expr(..)
) where

import Data.Text (Text)
import Facet.Core
import Facet.Core.Type
import Facet.Name
import Facet.Syntax

-- Term expressions

data Expr
  = XVar (Var Index)
  | XTLam Expr
  | XLam [(Pattern Name, Expr)]
  | XInst Expr TExpr
  | XApp Expr Expr
  | XCon (Q Name :$ Expr)
  | XString Text
  | XOp (Q Name) -- FIXME: this should have the arguments
  deriving (Eq, Ord, Show)
