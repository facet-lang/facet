module Facet.Core.Type
( -- * Kinds
  Kind(..)
  -- * Types
, Interface(..)
, Signature(..)
, fromInterfaces
, singleton
, interfaces
, mapSignature
, Type(..)
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

import Facet.Core.Interface
import Facet.Core.Kind
import Facet.Core.Type.Expr
import Facet.Core.Type.Norm
