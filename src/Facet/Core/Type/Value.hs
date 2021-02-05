module Facet.Core.Type.Value
( -- * Value types
  VType(..)
  -- * Computation types
, CType(..)
) where

import Facet.Name
import Facet.Stack
import Facet.Syntax
import Facet.Usage

-- Value types

data VType
  = VType
  | VInterface
  | VString
  | VSusp CType


-- Computation types

data CType
  = CForAll Name CType (CType -> CType)
  | CArrow (Maybe Name) Quantity CType CType
  | CNe (Var Meta Level) (Stack CType) (Stack CType)
  | CRet [CType] VType
