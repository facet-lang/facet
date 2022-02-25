module Facet.Elab.Pattern
( Clause(..)
, patterns_
, Tableau(..)
, clauses_
) where

import Facet.Pattern
import Fresnel.Iso

newtype Clause a = Clause [Pattern a]

patterns_ :: Iso' (Clause a) [Pattern a]
patterns_ = coerced

newtype Tableau a = Tableau [Clause a]

clauses_ :: Iso' (Tableau a) [Clause a]
clauses_ = coerced
