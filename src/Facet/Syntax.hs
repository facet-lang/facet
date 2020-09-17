{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
module Facet.Syntax
( -- * Expressions
  Expr(..)
, Inst(..)
, absurdI
, val
, lam0
, (<&)
, (&>)
  -- * Types
, Type(..)
  -- * Modules
, DeclName
, Module(..)
, Decl(..)
  -- * Signatures
, module Facet.Signature
) where

import Data.Functor.Sum
import Facet.Signature

-- Expressions

class (forall sig . Applicative (repr sig)) => Expr repr where
  -- FIXME: patterns
  lam :: (Either (repr None a) (Inst eff (repr (Sum eff sig) a)) -> repr sig b) -> repr sig (repr (Sum eff sig) a -> repr sig b)
  ($$) :: repr sig (repr sig' a -> repr sig b) -> repr sig' a -> repr sig b
  infixl 9 $$

  alg :: Inst sig (repr sig a) -> repr sig a

  weakenBy :: (forall x . sub x -> sup x) -> repr sub a -> repr sup a

  -- FIXME: constructors
  -- FIXME: patterns

data Inst eff a
  = forall k . Inst (eff k) (k -> a)

deriving instance Functor (Inst eff)

absurdI :: Inst None a -> b
absurdI (Inst e _) = absurd e


-- | Values embed into computations at every signature.
val :: Expr repr => repr None a -> repr sig a
val = weakenBy absurd

lam0 :: Expr repr => (repr None a -> repr sig b) -> repr sig (repr sig a -> repr sig b)
lam0 f = (. weakenBy InR) <$> lam (f . either id absurdI)


(<&) :: Expr repr => repr sig a -> repr sig b -> repr sig a
a <& b = fst' $$ a $$ b
  where
  fst' = lam0 (lam0 . const . val)

(&>) :: Expr repr => repr sig a -> repr sig b -> repr sig b
a &> b = snd' $$ a $$ b
  where
  snd' = lam0 (const (lam0 val))

infixl 1 <&, &>


-- Types

class Type ty where
  (-->) :: ty expr a -> ty expr b -> ty expr (expr a -> expr b)
  infixr 2 -->

  (.*) :: ty expr a -> ty expr b -> ty expr (a, b)
  infixl 7 .*

  (.$) :: ty expr (expr a -> expr b) -> ty expr a -> ty expr b
  infixl 9 .$

  _Unit :: ty expr ()


-- Modules

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
