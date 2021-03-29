module Facet.Norm
( Norm(..)
) where

import Data.Text (Text)
import Facet.Name
import Facet.Snoc

data Norm
  = NString Text
  | NCon RName (Snoc Norm)
