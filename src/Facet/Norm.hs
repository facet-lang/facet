module Facet.Norm
( Norm(..)
) where

import Data.Text (Text)
import Facet.Core.Pattern
import Facet.Name
import Facet.Snoc
import Facet.Syntax

data Norm
  = NString Text
  | NCon RName (Snoc Norm)
  | NLam [(Pattern Name, Pattern (Name :=: Norm) -> Norm)]
