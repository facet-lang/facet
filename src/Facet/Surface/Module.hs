{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Surface.Module
( Module(..)
, module'
, defTerm
, defType
, ModuleF(..)
, fold
) where

import Control.Effect.Parser.Span (Span)
import Facet.Name
import Facet.Surface.Decl (Decl)
import Facet.Surface.Expr (EName)
import Facet.Surface.Type (TName)

newtype Module = In { out :: ModuleF Module }

module' :: MName -> [Module] -> Module
module' = fmap In . Module

defTerm :: EName -> Decl -> Module
defTerm = fmap In . DefTerm

defType :: TName -> Decl -> Module
defType = fmap In . DefType

data ModuleF a
  = Module MName [a]
  | DefTerm EName Decl
  | DefType TName Decl
  | Ann Span a
  deriving (Foldable, Functor, Traversable)


fold :: (ModuleF a -> a) -> Module -> a
fold alg = go
  where
  go = alg . fmap go . out
