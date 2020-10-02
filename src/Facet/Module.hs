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
  | QName :.:. (Type.Type := Expr.Expr)

infix 1 :.:.

instance C.Module Expr.Expr Type.Type Module where
  module' = Module
  (.:.) = (:.:.)

interpret :: (C.Expr expr, C.Type ty, C.Module expr ty mod) => Module -> mod
interpret = \case
  Module n b -> C.module' n (interpret b)
  n :.:. ty := expr -> n C..:. Type.interpret ty := Expr.interpret expr
