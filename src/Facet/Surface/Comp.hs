{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Comp
( Comp(..)
) where

import Facet.Name
import Text.Parser.Position (Span, Spanned(..))

data Comp e
  = Cases [(Name, e)]
  | Expr e
  | Loc Span (Comp e)
  deriving (Foldable, Functor, Traversable)

instance Spanned (Comp e) where
  setSpan = Loc

  dropSpan = \case
    Loc _ d -> dropSpan d
    d       -> d
