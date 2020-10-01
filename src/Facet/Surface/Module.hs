{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Surface.Module
( Module(..)
) where

import qualified Facet.Surface as S
import           Facet.Surface.Decl (Decl)
import           Facet.Surface.Expr (Expr)
import           Facet.Surface.Type (Type)

data Module
  = S.DName :.:. Decl

infix 1 :.:.

instance S.Module Expr Type Decl Module where
  (.:.) = (:.:.)
