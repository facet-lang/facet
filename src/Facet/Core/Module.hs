{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Module
( Module(..)
, interpretModule
) where

import qualified Facet.Core as C
import qualified Facet.Core.Expr as Expr
import qualified Facet.Core.Type as Type
import           Facet.Name
import           Facet.Syntax

data Module = Module MName [(QName, C.Def Expr.Expr Type.Type ::: Type.Type)]

instance C.Module Expr.Expr Type.Type Module where
  module' = Module

interpretModule :: (C.Expr expr, C.Type ty, C.Module expr ty mod) => Module -> mod
interpretModule (Module n b) = C.module' n (map (fmap interpretDef) b)

interpretDef :: (C.Expr expr, C.Type ty) => (C.Def Expr.Expr Type.Type ::: Type.Type) -> C.Def expr ty ::: ty
interpretDef = \case
  C.DTerm e  ::: _T -> C.DTerm (Expr.interpret e)  ::: Type.interpret _T
  C.DType _T ::: _K -> C.DType (Type.interpret _T) ::: Type.interpret _K
