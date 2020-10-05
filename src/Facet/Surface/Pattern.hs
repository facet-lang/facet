{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Pattern
( Pattern(..)
, dropLoc
) where

import qualified Facet.Surface.Expr as S
import Text.Parser.Position (Located(..), Span)

data Pattern
  = Wildcard
  | Var S.EName
  | Tuple [Pattern]
  | Loc Span Pattern
  deriving (Eq, Ord, Show)

instance Located Pattern where
  locate = Loc

dropLoc :: Pattern -> Pattern
dropLoc = \case
  Loc _ e -> e
  e       -> e
