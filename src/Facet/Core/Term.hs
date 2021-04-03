module Facet.Core.Term
( -- * Term expressions
  Expr(..)
) where

import           Data.Text (Text)
import           Facet.Core.Pattern
import qualified Facet.Core.Type as T
import           Facet.Name
import           Facet.Syntax

-- Term expressions

data Expr
  = XVar (Var (LName Index))
  | XTLam Name Expr
  | XInst Expr T.TExpr
  | XLam [(Pattern Name, Expr)]
  | XApp Expr Expr
  | XCon RName [Expr]
  | XString Text
  | XDict [RName :=: Expr]
  deriving (Eq, Ord, Show)
