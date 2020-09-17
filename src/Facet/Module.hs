{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FunctionalDependencies #-}
module Facet.Module
( DeclName
, Module(..)
, Decl(..)
, prelude
) where

import Facet.Syntax
import Facet.Type

type DeclName = String

class (Decl expr ty decl, Applicative mod) => Module expr ty decl mod | mod -> decl ty expr where
  (.:) :: DeclName -> decl a -> mod (decl a)
  infixr 0 .:

class (Expr expr, Type ty) => Decl expr ty decl | decl -> ty expr where
  forAll :: (ty (expr sig) a -> decl b) -> decl b
  (>->) :: ty (expr sig) a -> (expr sig a -> decl b) -> decl (expr sig a -> b)
  infixr 1 >->
  (.=) :: ty (expr sig) a -> expr sig a -> decl a
  infix 1 .=


prelude :: Module expr ty decl mod => mod ()
prelude = do
  "id" .: forAll $ \ _A
    -> _A >-> \ x -> _A
    .= x
  "const" .: forAll $ \ _A -> forAll $ \ _B
    -> _A >-> \ x -> _B --> _A
    .= lam0 (const x)
  "unit" .: _Unit .= pure ()
  "flip" .: forAll $ \ _A -> forAll $ \ _B -> forAll $ \ _C
    -> (_A --> _B --> _C) >-> \ f -> _B >-> \ b -> _A >-> \ a -> _C
    .= f $$ a $$ b
  "curry" .: forAll $ \ _A -> forAll $ \ _B -> forAll $ \ _C
    -> ((_A .* _B) --> _C) >-> \ f -> _A >-> \ a -> _B >-> \ b -> _C
    .= f $$ ((,) <$> a <*> b)
  "curry" .: forAll $ \ _A -> forAll $ \ _B -> forAll $ \ _C
    -> (_A --> _B --> _C) >-> \ f -> _A .* _B >-> \ ab -> _C
    .= f $$ (fst <$> ab) $$ (snd <$> ab)
  pure ()
