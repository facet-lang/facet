module Facet.Sequent.Expr
( -- * Terms
  Term(..)
  -- * Coterms
, Coterm(..)
  -- * Commands
, Command(..)
) where

import Data.Text (Text)
import Facet.Name
import Facet.Pattern
import Facet.Syntax

-- Terms

data Term
  = Var (Var (LName Index))
  | MuR Name Command
  | FunR [(Pattern Name, Term)]
  | ConR RName [Term]
  | StringR Text
  | DictR [RName :=: Term]
  | CompR [RName :=: Name] Term


-- Coterms

data Coterm
  = Covar (Var (LName Index))
  | MuL Name Command
  | FunL Term Coterm


-- Commands

data Command = Term :|: Coterm
