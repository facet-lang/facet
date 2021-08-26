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
  | App (Ann Comment Expr) (Ann Comment Expr)
  | As (Ann Comment Expr) (Ann Comment Type)
  | String Text
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
