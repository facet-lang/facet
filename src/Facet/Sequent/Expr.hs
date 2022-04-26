module Facet.Sequent.Expr
( -- * Terms
  Term(..)
  -- * Coterms
, Coterm(..)
  -- * Commands
, Command(..)
  -- * Scopes
, ScopeLR
, ScopeL
, ScopeR
, BinderLR(..)
, BinderL(..)
, BinderR(..)
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

newtype ScopeL a = ScopeL { getScopeL :: a }

newtype ScopeR a = ScopeR { getScopeR :: a }

class BinderLR scope where
  abstractLR :: Name -> Name -> Command -> scope
  instantiateLR :: Term -> Coterm -> scope -> Command

class BinderL scope where
  abstractL :: Name -> Command -> scope
  instantiateL :: Coterm -> scope -> Command

class BinderR scope where
  abstractR :: Name -> Command -> scope
  instantiateR :: Term -> scope -> Command
