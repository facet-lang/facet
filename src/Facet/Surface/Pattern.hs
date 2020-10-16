{-# LANGUAGE DeriveTraversable #-}
module Facet.Surface.Pattern
( Pattern(..)
) where

import Text.Parser.Position

data Pattern a
  = Wildcard
  | Var a
  | Tuple [Spanned (Pattern a)]
  deriving (Foldable, Functor, Show, Traversable)
