{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Module
( Module(..)
, interpret
) where

import qualified Facet.Core as C
import qualified Facet.Core.Expr as Expr
import qualified Facet.Core.Type as Type
import           Facet.Name
import           Facet.Syntax

data Module
  = Module MName [Module]
  | DefTerm QName (Type.Type := Expr.Expr)

instance C.Module Expr.Expr Type.Type Module where
  module' = Module
  defTerm = DefTerm

interpret :: (C.Expr expr, C.Type ty, C.Module expr ty mod) => Module -> mod
interpret = \case
  Module n b -> C.module' n (map interpret b)
  DefTerm n (ty := expr) -> C.defTerm n (Type.interpret ty := Expr.interpret expr)
