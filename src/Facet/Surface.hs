{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface
( -- * Expressions
  Expr(..)
, unApp
, Comp(..)
, Pattern(..)
  -- * Types
, Type(..)
, unForAll
, unTApp
  -- * Declarations
, Decl(..)
, DDecl(..)
, unDDForAll
, TDecl(..)
, unTDForAll
  -- * Modules
, Module(..)
, Import(..)
) where

import Control.Effect.Empty
import Data.List.NonEmpty (NonEmpty)
import Facet.Name
import Facet.Syntax
import Text.Parser.Position

-- Expressions

data Expr
  = Qual QName
  | Free DName
  | Bound Index
  | Hole UName
  | Comp (Spanned Comp)
  | Spanned Expr :$ Spanned Expr
  -- FIXME: tupling/unit should take a list of expressions
  deriving (Show)

infixl 9 :$


unApp :: Has Empty sig m => Expr -> m (Spanned Expr, Spanned Expr)
unApp = \case
  f :$ a -> pure (f, a)
  _      -> empty


data Comp
  = Expr (Spanned Expr)
  | Clauses [(NonEmpty (Spanned Pattern), Spanned Expr)]
  deriving (Show)


data Pattern
  = PVar UName
  | PCon CName [Spanned Pattern]
  deriving (Show)


-- Types

data Type
  = TQual QName
  | TFree DName
  | TBound Index
  | THole UName
  | Type
  | (UName ::: Spanned Type) :=> Spanned Type
  | Spanned Type :$$ Spanned Type
  | Spanned Type :-> Spanned Type
  deriving (Show)

infixr 1 :=>
infixl 9 :$$
infixr 2 :->


unForAll :: Has Empty sig m => Type -> m (UName ::: Spanned Type, Spanned Type)
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unTApp :: Has Empty sig m => Type -> m (Spanned Type, Spanned Type)
unTApp = \case{ f :$$ a -> pure (f, a) ; _ -> empty }


-- Declarations

data Decl
  = DDecl (Spanned DDecl)
  | TDecl (Spanned TDecl)
  deriving Show

data DDecl
  = DDForAll (Pl_ UName ::: Spanned Type) (Spanned DDecl)
  | DDBody (Spanned Type) [Spanned (CName ::: Spanned Type)]
  deriving (Show)

unDDForAll :: Has Empty sig m => DDecl -> m (Pl_ UName ::: Spanned Type, Spanned DDecl)
unDDForAll = \case{ DDForAll t b -> pure (t, b) ; _ -> empty }


data TDecl
  = TDForAll (Pl_ UName ::: Spanned Type) (Spanned TDecl)
  | TDBody (Spanned Type) (Spanned Expr)
  deriving (Show)

unTDForAll :: Has Empty sig m => TDecl -> m (Pl_ UName ::: Spanned Type, Spanned TDecl)
unTDForAll = \case{ TDForAll t b -> pure (t, b) ; _ -> empty }


-- Modules

data Module = Module { name :: MName, imports :: [Spanned Import], defs :: [Spanned (DName, Spanned Decl)] }
  deriving (Show)

newtype Import = Import { name :: MName }
  deriving (Show)
