{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Core.Pattern
( Pattern(..)
) where

import Facet.Vars

data Pattern a
  = Wildcard
  | Var a
  | Tuple [Pattern a]
  deriving (Foldable, Functor, Show, Traversable)

instance Scoped a => Scoped (Pattern a) where
  fvs = \case
    Wildcard -> mempty
    Var n    -> fvs n
    Tuple ps -> foldMap fvs ps
