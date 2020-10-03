{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface
( EName(..)
, Expr(..)
, TName(..)
, Type(..)
, Module(..)
, Decl(..)
, (:::)(..)
, Located(..)
) where

import Control.Effect.Parser.Span (Span)
import Data.String (IsString(..))
import Data.Text (Text)
import Facet.Name
import Facet.Syntax ((:::)(..))
import Prettyprinter (Pretty)

newtype EName = EName { getEName :: Text }
  deriving (Eq, IsString, Ord, Pretty, Show)

class Expr expr where
  global :: EName -> expr
  bound :: Name -> expr

  lam :: Name -> expr -> expr
  ($$) :: expr -> expr -> expr
  infixl 9 $$

  unit :: expr
  -- | Tupling.
  (**) :: expr -> expr -> expr
  -- FIXME: tupling/unit should take a list of expressions


newtype TName = TName { getTName :: Text }
  deriving (Eq, IsString, Ord, Pretty, Show)

class Type ty where
  tglobal :: TName -> ty
  tbound :: Name -> ty

  (>~>) :: (Name ::: ty) -> ty -> ty
  infixr 1 >~>

  (-->) :: ty -> ty -> ty
  infixr 2 -->

  (.$) :: ty -> ty -> ty
  infixl 9 .$

  (.*) :: ty -> ty -> ty
  infixl 7 .*
  -- FIXME: tupling/unit should take a list of types

  _Unit :: ty
  _Type :: ty


class Decl expr ty decl => Module expr ty decl mod | mod -> decl where
  module' :: MName -> [mod] -> mod
  defTerm :: EName -> decl -> mod
  defType :: TName -> decl -> mod

class (Expr expr, Type ty) => Decl expr ty decl | decl -> ty expr where
  -- | Universal quantification.
  (>=>) :: (Name ::: ty) -> decl -> decl
  infixr 1 >=>

  (>->) :: (Name ::: ty) -> decl -> decl
  infixr 1 >->

  (.=) :: ty -> expr -> decl
  infix 1 .=


class Located expr where
  locate :: Span -> expr -> expr
