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

data Module = Module MName [(QName, Def ::: Type.Type)]

instance C.Module Type.Type Def Module where
  module' = Module

interpretModule :: (C.Expr expr, C.Type ty, C.Def expr ty def, C.Module ty def mod) => Module -> mod
interpretModule (Module n b) = C.module' n (map (fmap interpretDef) b)

interpretDef :: (C.Expr expr, C.Type ty, C.Def expr ty def) => (Def ::: Type.Type) -> def ::: ty
interpretDef = \case
  DefTerm e  ::: _T -> C.defTerm (Expr.interpret e)  ::: Type.interpret _T
  DefType _T ::: _K -> C.defType (Type.interpret _T) ::: Type.interpret _K


data Def
  = DefTerm Expr.Expr
  | DefType Type.Type

instance C.Def Expr.Expr Type.Type Def where
  defType = DefType
  defTerm = DefTerm
