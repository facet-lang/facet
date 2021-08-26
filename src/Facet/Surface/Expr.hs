{-# LANGUAGE UndecidableInstances #-}
module Facet.Surface.Expr
( -- * Types
  Kind(..)
, Type(..)
, Mul(..)
  -- * Expressions
, Expr(..)
, Interface(..)
, Clause(..)
  -- * Patterns
, Pattern(..)
, ValPattern(..)
, EffPattern(..)
  -- * Definitions
, Def(..)
  -- * Modules
, Module(..)
, Import(..)
) where

import Data.Text (Text)
import Facet.Name
import Facet.Snoc
import Facet.Syntax

-- Types

data Kind
  = KType
  | KInterface
  | KArrow (Maybe Name) (Ann Comment Kind) (Ann Comment Kind)
  deriving (Eq, Show)

data Type
  = TVar QName
  | TString
  | TForAll Name (Ann Comment Kind) (Ann Comment Type)
  | TArrow (Maybe Name) (Maybe Mul) (Ann Comment Type) (Ann Comment Type)
  | TComp [Ann Comment Interface] (Ann Comment Type)
  | TApp (Ann Comment Type) (Ann Comment Type)
  deriving (Eq, Show)

data Mul = Zero | One
  deriving (Bounded, Enum, Eq, Ord, Show)


-- Expressions

data Expr
  = Var QName
  | Hole Name
  | Lam [Clause]
  | App (Ann Comment Expr) (Ann Comment Expr)
  | As (Ann Comment Expr) (Ann Comment Type)
  | String Text
  deriving (Eq, Show)


data Interface = Interface (Ann Comment QName) (Snoc (Ann Comment Type))
  deriving (Eq, Show)


data Clause = Clause (Ann Comment Pattern) (Ann Comment Expr)
  deriving (Eq, Show)


-- Patterns

data Pattern
  = PVal (Ann Comment ValPattern)
  | PEff (Ann Comment EffPattern)
  deriving (Eq, Show)

data ValPattern
  = PWildcard
  | PVar Name
  | PCon QName [Ann Comment ValPattern]
  deriving (Eq, Show)

data EffPattern = POp QName [Ann Comment ValPattern] (Ann Comment ValPattern)
  deriving (Eq, Show)


-- Declarations

data Def
  = DataDef [Ann Comment (Name ::: Ann Comment Type)] (Ann Comment Kind)
  | InterfaceDef [Ann Comment (Name ::: Ann Comment Type)] (Ann Comment Kind)
  | TermDef (Ann Comment Expr) (Ann Comment Type)
  deriving (Eq, Show)


-- Modules

data Module = Module
  { name      :: MName
  , imports   :: [Ann Comment Import]
  -- FIXME: store source references for operators’ definitions, for error reporting
  , operators :: [(Op, Assoc)]
  , defs      :: [Ann Comment (Name, Ann Comment Def)]
  }
  deriving (Eq, Show)


newtype Import = Import { name :: MName }
  deriving (Eq, Show)
