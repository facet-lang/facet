{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Surface.Module
( Module(..)
) where

import           Facet.Name
import qualified Facet.Surface as S
import           Facet.Surface.Decl (Decl)
import           Facet.Surface.Expr (Expr)
import           Facet.Surface.Type (Type)

data Module
  = Module MName [Module]
  | DefTerm S.EName Decl
  | DefType S.TName Decl

instance S.Module Expr Type Decl Module where
  module' = Module
  defTerm = DefTerm
  defType = DefType
