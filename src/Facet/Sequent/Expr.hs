module Facet.Sequent.Expr
( -- * Terms
  Term(..)
  -- * Coterms
, Coterm(..)
  -- * Commands
, Command(..)
  -- * Scopes
, ScopeLR
, BinderL(..)
) where

import Data.Text (Text)
import Facet.Name
import Facet.Syntax

-- Terms

data Term
  = Var (Var Index)
  | MuR Command
  | LamR Command
  | SumR Int Term
  | BottomR Command
  | UnitR
  | PrdR Term Term
  | StringR Text


-- Coterms

data Coterm
  = Covar (Var Index)
  | MuL Command
  | LamL Term Coterm
  | SumL [Coterm]
  | UnitL
  | PrdL1 Coterm
  | PrdL2 Coterm


-- Commands

data Command
  = Term :|: Coterm
  | Let Term Command


-- Scopes

newtype ScopeLR = ScopeLR { getScopeLR :: Command }

class BinderL scope where
  abstractL :: Name -> Command -> scope
  instantiateL :: Command -> scope -> Command
