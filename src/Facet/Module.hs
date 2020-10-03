{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Module
( Module(..)
, interpret
) where

import qualified Facet.Core as C
import qualified Facet.Expr as Expr
import           Facet.Name
import           Facet.Syntax
import qualified Facet.Type as Type

data Module
  = Module MName Module
  | DefTerm QName (Type.Type := Expr.Expr)

instance C.Module Expr.Expr Type.Type Module where
  module' = Module
  defTerm = DefTerm

interpret :: (C.Expr expr, C.Type ty, C.Module expr ty mod) => Module -> mod
interpret = \case
  Module n b -> C.module' n (interpret b)
  DefTerm n (ty := expr) -> C.defTerm n (Type.interpret ty := Expr.interpret expr)
