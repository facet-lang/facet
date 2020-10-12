{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
module Facet.Surface.Module
( Module(..)
) where

import Facet.Name
import Facet.Surface.Decl (Decl)

-- FIXME: imports
data Module f a = Module { name :: MName, defs :: [f (DName, f (Decl f a))] }
  deriving (Foldable, Functor, Traversable)

deriving instance (Show a, forall a . Show a => Show (f a)) => Show (Module f a)
