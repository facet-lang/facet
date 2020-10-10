{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Surface.Module
( Module(..)
, Def(..)
) where

import Facet.Name
import Facet.Surface.Decl (Decl)

-- FIXME: imports
data Module a = Module { ann :: a, name :: MName, defs :: [Def a] }
  deriving (Foldable, Functor, Show, Traversable)

data Def a = Def a DName (Decl a)
  deriving (Foldable, Functor, Show, Traversable)
