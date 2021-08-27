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
  = DataDef [Ann Comment (Name ::: Ann Comment Type)] Kind
  | InterfaceDef [Ann Comment (Name ::: Ann Comment Type)] Kind
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
