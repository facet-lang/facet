{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Core.Pattern
( Pattern(..)
, unsafeGetVar
) where

import GHC.Stack

-- FIXME: represent wildcard patterns as var patterns with an empty name.
data Pattern a
  = Wildcard
  | Var a
  | Tuple [Pattern a]
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

unsafeGetVar :: HasCallStack => Pattern a -> a
unsafeGetVar = \case
  Var a -> a
  _     -> error "unsafeGetVar: non-Var pattern"
