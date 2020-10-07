{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Module
( Module(..)
, interpretModule
, interpretDef
, Def(..)
) where

import qualified Facet.Core as C
import qualified Facet.Core.Expr as Expr
import qualified Facet.Core.Type as Type
import           Facet.Name
import           Facet.Syntax

data Module = Module MName [Def]

instance C.Module Def Module where
  module' = Module

interpretModule :: (C.Expr expr, C.Type ty, C.Def expr ty def, C.Module def mod) => Module -> mod
interpretModule (Module n b) = C.module' n (map interpretDef b)

interpretDef :: (C.Expr expr, C.Type ty, C.Def expr ty def) => Def -> def
interpretDef (DefTerm n (ty := expr)) = C.defTerm n (Type.interpret ty := Expr.interpret expr)


data Def = DefTerm QName (Type.Type := Expr.Expr)

instance C.Def Expr.Expr Type.Type Def where
  defTerm = DefTerm
