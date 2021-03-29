module Facet.Norm
( Norm(..)
, Elim(..)
) where

import Data.Text (Text)
import Facet.Core.Pattern
import Facet.Core.Type (Type)
import Facet.Name
import Facet.Snoc
import Facet.Syntax

data Norm
  = NString Text
  | NCon RName (Snoc Norm)
  | NLam [(Pattern Name, Pattern (Name :=: Norm) -> Norm)]
  | NNe (Var (LName Level)) (Snoc Elim)

data Elim
  = EApp Norm
  | EInst Type
