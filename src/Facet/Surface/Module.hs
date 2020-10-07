{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Surface.Module
( Module(..)
, module'
, def
, ModuleF(..)
) where

import Facet.Name
import Facet.Surface.Decl (Decl)
import Text.Parser.Position (Span)

data Module = In { ann :: Span, out :: ModuleF Module }

module' :: Span -> MName -> [Module] -> Module
module' s = fmap (In s) . Module

def :: Span -> DName -> Decl -> Module
def s = fmap (In s) . Def

data ModuleF a
  = Module MName [a]
  | Def DName Decl
  deriving (Foldable, Functor, Traversable)
