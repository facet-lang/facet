module Facet.Term.Class
( Term(..)
) where

import Data.Text (Text)
import Facet.Name
import Facet.Pattern
import Facet.Syntax

class Term r where
  string :: Text -> r
  con :: RName -> [r] -> r
  lam :: [(Pattern Name, Pattern (Name :=: r) -> r)] -> r
  var :: Var (LName Level) -> r
  ($$) :: r -> r -> r
  infixl 9 $$
  dict :: [RName :=: r] -> r
  comp :: [RName :=: Name] -> (Pattern (Name :=: r) -> r) -> r
