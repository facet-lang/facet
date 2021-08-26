module Facet.Term.Class
( Term(..)
, lamA
) where

import Data.Text (Text)
import Facet.Functor.Compose
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


lamA :: (Applicative m, Applicative i, Term r) => (forall j . Applicative j => (i ~> j) -> [(Pattern Name, j (Pattern (Name :=: r)) -> m (j r))]) -> m (i r)
lamA b = fmap lam . traverse (traverse runC) <$> traverse (traverse ($ liftCInner id)) (b liftCOuter)
