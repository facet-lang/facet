module Facet.Env
( Env(..)
, (|>)
) where

import Facet.Core.Pattern
import Facet.Name
import Facet.Snoc
import Facet.Syntax

newtype Env v = Env { bindings :: Snoc (Pattern (Name :=: v)) }

(|>) :: Env v -> Pattern (Name :=: v) -> Env v
Env vs |> v = Env (vs :> v)

infixl 5 |>
