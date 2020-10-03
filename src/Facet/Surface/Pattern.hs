module Facet.Surface.Pattern
( Pattern(..)
) where

import qualified Facet.Surface as S

data Pattern
  = Wildcard
  | Var S.EName
  deriving (Eq, Ord, Show)
