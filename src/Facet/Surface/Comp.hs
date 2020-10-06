{-# LANGUAGE DeriveTraversable #-}
module Facet.Surface.Comp
( Comp(..)
) where

import Facet.Name
import Text.Parser.Position (Span)

data Comp e
  = Cases [(Name, e)]
  | Expr e
  | Loc Span (Comp e)
  deriving (Foldable, Functor, Traversable)
