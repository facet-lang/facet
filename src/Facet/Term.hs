module Facet.Term
( -- * Term expressions
  Expr(..)
) where

import Data.Text (Text)
import Facet.Name
import Facet.Pattern
import Facet.Syntax

-- Term expressions

data Expr
  = XVar (Var (LName Index))
  | XLam [(Pattern Name, Expr)]
  | XApp Expr Expr
  | XCon RName [Expr]
  | XString Text
  | XDict [RName :=: Expr]
  | XLet (Pattern Name) Expr Expr
  | XComp [RName :=: Name] Expr -- ^ NB: the first argument is a specialization of @'Pattern' 'Name'@ to the 'PDict' constructor
  deriving (Eq, Ord, Show)
