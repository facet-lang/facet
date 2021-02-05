module Facet.Core.Type.Expr
( -- * Variables
  TVar(..)
  -- * Value types
, VTExpr(..)
  -- * Computation types
, CTExpr(..)
) where

import Facet.Name
import Facet.Usage

-- Variables

data TVar a
  = TGlobal (Q Name) -- ^ Global variables, considered equal by 'Q' 'Name'.
  | TFree a
  | TMetavar Meta
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


-- Value types

data VTExpr
  = VEType
  | VEInterface
  | VEString
  | VESusp CTExpr
  deriving (Eq, Ord, Show)


-- Computation types

data CTExpr
  = CEVar (TVar Index)
  | CEForAll Name CTExpr CTExpr
  | CEArrow (Maybe Name) Quantity CTExpr CTExpr
  | CEInst CTExpr CTExpr
  | CEApp CTExpr CTExpr
  | CERet [CTExpr] VTExpr
  deriving (Eq, Ord, Show)
