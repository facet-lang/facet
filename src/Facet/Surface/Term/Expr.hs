module Facet.Surface.Term.Expr
( -- * Expressions
  Expr(..)
, Clause(..)
  -- * Patterns
, Pattern(..)
, ValPattern(..)
, EffPattern(..)
) where

import Data.Text (Text)
import Facet.Name
import Facet.Surface.Type.Expr
import Facet.Syntax

-- Expressions

data Expr
  = Var QName
  | Hole Name
  | Lam [Clause]
  | App (Ann Expr) (Ann Expr)
  | As (Ann Expr) (Ann Type)
  | String Text
  deriving (Eq, Show)


data Clause = Clause (Ann Pattern) (Ann Expr)
  deriving (Eq, Show)


-- Patterns

data Pattern
  = PVal (Ann ValPattern)
  | PEff (Ann EffPattern)
  deriving (Eq, Show)

data ValPattern
  = PWildcard
  | PVar Name
  | PCon QName [Ann ValPattern]
  deriving (Eq, Show)

data EffPattern = POp QName [Ann ValPattern] (Ann ValPattern)
  deriving (Eq, Show)
