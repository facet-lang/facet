{-# LANGUAGE DeriveTraversable #-}
module Facet.Surface.Comp
( Comp(..)
) where

import Facet.Name

data Comp e
  = Cases [(Name, e)]
  | Expr e
  deriving (Foldable, Functor, Traversable)
