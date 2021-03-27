module Facet.Core.Term
( -- * Term expressions
  Expr(..)
) where

import           Data.Text (Text)
import           Facet.Core.Pattern
import qualified Facet.Core.Type as T
import           Facet.Name
import           Facet.Snoc
import           Facet.Syntax

-- Term expressions

data Expr
  = XVar (Var Index)
  | XTLam Expr
  | XInst Expr T.TExpr
  | XLam [(Pattern Name, Expr)]
  | XApp Expr Expr
  | XCon RName (Snoc T.TExpr) (Snoc Expr)
  | XString Text
  | XOp RName (Snoc T.TExpr) (Snoc Expr)
  deriving (Eq, Ord, Show)
