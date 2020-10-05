{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Pattern
( Pattern(..)
, dropLoc
) where

import Facet.Name
import Text.Parser.Position (Spanned(..), Span)

data Pattern
  = Wildcard
  | Var EName
  | Tuple [Pattern]
  | Loc Span Pattern
  deriving (Eq, Ord, Show)

instance Spanned Pattern where
  setSpan = Loc

dropLoc :: Pattern -> Pattern
dropLoc = \case
  Loc _ e -> e
  e       -> e
