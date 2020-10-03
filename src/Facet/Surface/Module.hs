{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Surface.Module
( Module(..)
, ModuleF(..)
, fold
) where

import           Facet.Name
import qualified Facet.Surface as S
import           Facet.Surface.Decl (Decl)
import           Facet.Surface.Expr (Expr)
import           Facet.Surface.Type (Type)

newtype Module = In { out :: ModuleF Module }

data ModuleF a
  = Module MName [a]
  | DefTerm S.EName Decl
  | DefType S.TName Decl
  deriving (Foldable, Functor, Traversable)

instance S.Module Expr Type Decl Module where
  module' = fmap In . Module
  defTerm = fmap In . DefTerm
  defType = fmap In . DefType


fold :: (ModuleF a -> a) -> Module -> a
fold alg = go
  where
  go = alg . fmap go . out
