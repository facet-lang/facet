module Facet.Elab.Pattern
( Clause(..)
) where

import Facet.Pattern

newtype Clause = Clause [Pattern ()]
