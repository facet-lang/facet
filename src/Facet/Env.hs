module Facet.Env
( Env(..)
) where

import Facet.Name
import Facet.Snoc
import Facet.Syntax

newtype Env v = Env { bindings :: Snoc (Name :=: v) }
