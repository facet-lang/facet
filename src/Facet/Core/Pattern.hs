{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Core.Pattern
( Pattern(..)
) where

import Facet.Name

data Pattern a
  = Wildcard
  | Var a
  | Tuple [Pattern a]
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Scoped a => Scoped (Pattern a) where
  fvs = \case
    Wildcard -> mempty
    Var n    -> fvs n
    Tuple ps -> foldMap fvs ps
