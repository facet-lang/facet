module Facet.Core.Type
( -- * Types
  Type(..)
, global
, free
, metavar
, unNeutral
, unComp
, Classifier(..)
, classifierType
, occursIn
  -- ** Elimination
, ($$)
, ($$*)
  -- * Type expressions
, TExpr(..)
  -- * Quotation
, quote
, eval
, apply
) where

import Facet.Core.Type.Expr
import Facet.Core.Type.Norm
