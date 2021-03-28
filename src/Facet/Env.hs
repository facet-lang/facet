module Facet.Env
( Env(..)
) where

import Facet.Core.Pattern
import Facet.Name
import Facet.Snoc
import Facet.Syntax

newtype Env v = Env { bindings :: Snoc (Pattern (Name :=: v)) }
