module Facet.Core.Term
( -- * Term values
  Value(..)
  -- * Term expressions
, Expr(..)
) where

import Data.Text (Text)
import Facet.Core
import Facet.Core.Type
import Facet.Name
import Facet.Syntax

-- Term values

data Value
  = VTLam (Type -> Value)
  | VLam [(Pattern Name, Pattern Value -> Value)]
  | VNe (Var Level :$ Either Type Value)
  | VCon (Q Name :$ Value)
  | VString Text
  | VOp (Q Name :$ Value)


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
