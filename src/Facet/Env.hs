module Facet.Env
( Env(..)
, empty
, (|>)
, index
, level
) where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.Maybe (fromMaybe)
import Facet.Core.Pattern
import Facet.Name
import Facet.Snoc
import Facet.Syntax
import GHC.Stack

newtype Env v = Env { bindings :: Snoc (Pattern (Name :=: v)) }

empty :: Env v
empty = Env Nil

(|>) :: Env v -> Pattern (Name :=: v) -> Env v
Env vs |> v = Env (vs :> v)

infixl 5 |>

index :: HasCallStack => Env v -> Index -> Name -> v
index (Env vs) i n = fromMaybe (error ("Env.index: name (" <> show n <> ") not found")) (find (\ (n' :=: v) -> v <$ guard (n == n')) (vs ! getIndex i))
  where
  find f = foldr ((<|>) . f) Nothing

level :: Env v -> Level
level = Level . length . bindings
