module Facet.Surface.Pattern
( Pattern(..)
) where

import qualified Facet.Surface.Expr as S

data Pattern
  = Wildcard
  | Var S.EName
  | Tuple [Pattern]
  deriving (Eq, Ord, Show)
