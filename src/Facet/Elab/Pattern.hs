module Facet.Elab.Pattern
( Clause(..)
, patterns_
, Tableau(..)
, clauses_
) where

import Facet.Pattern
import Fresnel.Iso

newtype Clause = Clause [Pattern ()]

patterns_ :: Iso' Clause [Pattern ()]
patterns_ = coerced

newtype Tableau = Tableau [Clause]

clauses_ :: Iso' Tableau [Clause]
clauses_ = coerced
