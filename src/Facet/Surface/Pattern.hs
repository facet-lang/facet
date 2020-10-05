{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Pattern
( Pattern(..)
, dropLoc
) where

import Facet.Name
import Text.Parser.Position (Spanned(..), Span)

data Pattern a
  = Wildcard
  | Var EName
  | Tuple [Pattern a]
  | Loc Span (Pattern a)
  deriving (Eq, Ord, Show)

instance Spanned (Pattern a) where
  setSpan = Loc

dropLoc :: Pattern a -> Pattern a
dropLoc = \case
  Loc _ e -> e
  e       -> e
