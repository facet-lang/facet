{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Decl
( Decl(..)
) where

import Facet.Name
import Facet.Surface.Expr (Expr)
import Facet.Surface.Type (Type)
import Facet.Syntax

data Decl
  = Type := Expr
  | (Name ::: Type) :=> Decl
  | (Name ::: Type) :-> Decl

infix 1 :=
infixr 1 :=>
infixr 1 :->
