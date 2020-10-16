{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
module Facet.Surface.Module
( Module(..)
) where

import Facet.Name
import Facet.Surface.Decl (Decl)
import Text.Parser.Position

-- FIXME: imports
data Module a = Module { name :: MName, defs :: [Spanned (DName, Spanned (Decl Spanned a))] }
  deriving (Foldable, Functor, Show, Traversable)
