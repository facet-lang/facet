module Facet.Core.Type.Expr
( -- * Value types
  VTExpr(..)
  -- * Computation types
, CTExpr(..)
) where

import Facet.Name
import Facet.Syntax
import Facet.Usage

-- Value types

data VTExpr
  = VEType
  | VEInterface
  | VEString
  | VESusp CTExpr
  deriving (Eq, Ord, Show)


-- Computation types

data CTExpr
  = CEVar (Var Meta Index)
  | CEForAll Name CTExpr CTExpr
  | CEArrow (Maybe Name) Quantity CTExpr CTExpr
  | CEInst CTExpr CTExpr
  | CEApp CTExpr CTExpr
  | CERet [CTExpr] VTExpr
  deriving (Eq, Ord, Show)
