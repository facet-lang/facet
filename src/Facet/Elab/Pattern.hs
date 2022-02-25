{-# LANGUAGE ExistentialQuantification #-}
module Facet.Elab.Pattern
( Clause(..)
, patterns_
, Tableau(..)
, clauses_
, Branch(..)
) where

import Facet.Pattern
import Fresnel.Fold
import Fresnel.Iso

newtype Clause a = Clause [Pattern a]

patterns_ :: Iso' (Clause a) [Pattern a]
patterns_ = coerced

newtype Tableau a = Tableau [Clause a]

clauses_ :: Iso' (Tableau a) [Clause a]
clauses_ = coerced


data Branch s m a = forall x . Branch (Fold s x) (x -> m a)
