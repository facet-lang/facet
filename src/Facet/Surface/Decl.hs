{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Decl
( Decl(..)
) where

import Facet.Expr (Expr)
import Facet.Name
import Facet.Syntax
import Facet.Type (Type)

data Decl
  = Type := Expr
  | (Name ::: Type) :=> Decl
  | (Name ::: Type) :-> Decl

infix 1 :=
infixr 1 :=>
infixr 1 :->
