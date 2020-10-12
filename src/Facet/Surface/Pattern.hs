{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
module Facet.Surface.Pattern
( Pattern(..)
) where

data Pattern f a
  = Wildcard
  | Var a
  | Tuple [f (Pattern f a)]
  deriving (Foldable, Functor, Traversable)

deriving instance (Show a, forall a . Show a => Show (f a)) => Show (Pattern f a)
