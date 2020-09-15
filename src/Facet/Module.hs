{-# LANGUAGE FunctionalDependencies #-}
module Facet.Module
( DeclName
, Module(..)
, Decl(..)
) where

import Facet.Expr
import Facet.Type

type DeclName = String

class (Decl expr ty decl, Applicative mod) => Module expr ty decl mod | mod -> decl ty expr where
  (.:) :: DeclName -> decl a -> mod (decl a)
  infixr 0 .:

class (Expr expr, Type ty) => Decl expr ty decl | decl -> ty expr where
  forAll :: (ty (expr sig) a -> decl b) -> decl b
  (>->) :: ty (expr sig) a -> (expr sig a -> decl b) -> decl (expr sig a -> b)
  (.=) :: ty (expr sig) a -> expr sig a -> decl a
  infix 1 .=
