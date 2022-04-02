{-# LANGUAGE UndecidableInstances #-}
module Facet.Surface.Module
( -- * Definitions
  Def(..)
  -- * Modules
, Module(..)
, Import(..)
) where

import Facet.Kind
import Facet.Name
import Facet.Surface.Term.Expr
import Facet.Surface.Type.Expr
import Facet.Syntax

-- Declarations

data Def
  = DataDef [Ann (Name ::: Ann Type)] Kind
  | InterfaceDef [Ann (Name ::: Ann Type)] Kind
  | TermDef (Ann Expr) (Ann Type)
  deriving (Eq, Show)


-- Modules

data Module = Module
  { name      :: QName
  , imports   :: [Ann Import]
  -- FIXME: store source references for operators’ definitions, for error reporting
  , operators :: [(Op, Assoc)]
  , defs      :: [Ann (Name, Ann Def)]
  }
  deriving (Eq, Show)


newtype Import = Import { name :: QName }
  deriving (Eq, Show)
