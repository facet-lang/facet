module Facet.Sequent.Expr
( -- * Terms
  Term(..)
  -- * Coterms
, Coterm(..)
  -- * Commands
, (C.:|:)(..)
) where

import           Data.Text (Text)
import           Facet.Name
import           Facet.Pattern
import qualified Facet.Sequent.Class as C
import           Facet.Syntax

-- Terms

data Term
  = Var (Var (LName Index))
  | MuR Name (Term C.:|: Coterm)
  | FunR [(Pattern Name, Term)]
  | ConR RName [Term]
  | StringR Text
  | DictR [RName :=: Term]
  | CompR [RName :=: Name] Term


-- Coterms

data Coterm
  = Covar (Var (LName Index))
  | MuL Name (Term C.:|: Coterm)
  | FunL Term Coterm
