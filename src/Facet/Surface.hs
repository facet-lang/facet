{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface
( EName(..)
, Expr(..)
, TName(..)
, Type(..)
, ForAll(..)
, DName(..)
, Module(..)
, Decl(..)
, (:::)(..)
, Located(..)
, LocationParsing(..)
) where

import Control.Effect.Parser.Span (Pos, Span)
import Data.String (IsString(..))
import Data.Text (Text)
import Facet.Syntax ((:::)(..))
import Prettyprinter (Pretty)
import Text.Parser.Token (TokenParsing)

newtype EName = EName { getEName :: Text }
  deriving (Eq, IsString, Ord, Pretty, Show)

class Expr expr where
  global :: EName -> expr

  lam0 :: EName -> (expr -> expr) -> expr
  lam :: EName -> (Either expr (expr, expr -> expr) -> expr) -> expr
  ($$) :: expr -> expr -> expr
  infixl 9 $$

  unit :: expr
  -- | Tupling.
  (**) :: expr -> expr -> expr
  -- FIXME: tupling/unit should take a list of expressions


class ForAll ty decl | decl -> ty where
  -- | Universal quantification.
  (>=>) :: (TName ::: ty) -> (ty -> decl) -> decl
  infixr 1 >=>


newtype TName = TName { getTName :: Text }
  deriving (Eq, IsString, Ord, Pretty, Show)

class ForAll ty ty => Type ty where
  tglobal :: TName -> ty

  (-->) :: ty -> ty -> ty
  infixr 2 -->

  (.$) :: ty -> ty -> ty
  infixl 9 .$

  (.*) :: ty -> ty -> ty
  infixl 7 .*
  -- FIXME: tupling/unit should take a list of types

  _Unit :: ty
  _Type :: ty


newtype DName = DName { getDeclName :: Text }
  deriving (Eq, IsString, Ord, Pretty, Show)

-- FIXME: define a core variant of this where declarations are normalized to not contain term bindings in the signature but instead pattern match in the definition
class Decl expr ty decl => Module expr ty decl mod | mod -> decl where
  (.:) :: DName -> decl -> mod
  infixr 0 .:

class (Expr expr, ForAll ty decl, Type ty) => Decl expr ty decl | decl -> ty expr where
  (.=) :: ty -> expr -> decl
  infix 1 .=

  (>->) :: (EName ::: ty) -> (expr -> decl) -> decl
  infixr 1 >->


class Located expr where
  locate :: Span -> expr -> expr

class TokenParsing p => LocationParsing p where
  position :: p Pos
