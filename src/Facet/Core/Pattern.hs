{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Core.Pattern
( Pattern(..)
) where

data Pattern a
  = Wildcard
  | Var a
  | Tuple [Pattern a]
  deriving (Foldable, Functor, Show, Traversable)
