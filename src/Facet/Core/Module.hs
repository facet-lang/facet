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

data Module = Module MName [(QName, Def)]

instance C.Module Def Module where
  module' = Module

interpretModule :: (C.Expr expr, C.Type ty, C.Def expr ty def, C.Module def mod) => Module -> mod
interpretModule (Module n b) = C.module' n (map (fmap interpretDef) b)

interpretDef :: (C.Expr expr, C.Type ty, C.Def expr ty def) => Def -> def
interpretDef = \case
  DefTerm (_T := e)  -> C.defTerm (Type.interpret _T := Expr.interpret e)
  DefType (_K := _T) -> C.defType (Type.interpret _K := Type.interpret _T)


data Def
  = DefTerm (Type.Type := Expr.Expr)
  | DefType (Type.Type := Type.Type)

instance C.Def Expr.Expr Type.Type Def where
  defType = DefType
  defTerm = DefTerm
