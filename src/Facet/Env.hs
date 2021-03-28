module Facet.Env
( Env(..)
, (|>)
, index
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

(|>) :: Env v -> Pattern (Name :=: v) -> Env v
Env vs |> v = Env (vs :> v)

infixl 5 |>

index :: HasCallStack => Env v -> Index -> Name -> v
index (Env vs) i n = fromMaybe (error ("Env.index: name (" <> show n <> ") not found")) (find (\ (n' :=: v) -> v <$ guard (n == n')) (vs ! getIndex i))
  where
  find f = foldr ((<|>) . f) Nothing
