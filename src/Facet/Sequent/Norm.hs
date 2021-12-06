module Facet.Sequent.Norm
( -- * Terms
  Term(..)
  -- * Coterms
, Coterm(..)
  -- * Commands
, Command(..)
) where

import           Data.Text (Text)
import           Facet.Name
import           Facet.Pattern
import           Facet.Syntax hiding (Var)
import qualified Facet.Syntax as Syntax

-- Terms

data Term
  = Var (Syntax.Var (LName Level))
  | MuR (Coterm -> Command)
  | FunR [(Pattern Name, Pattern (Name :=: Term) -> Term)]
  | ConR RName [Term]
  | StringR Text
  | DictR [RName :=: Term]
  | CompR [RName :=: Name] (Pattern (Name :=: Term) -> Term)


-- Coterms

data Coterm
  = Covar (Syntax.Var (LName Level))
  | MuL (Term -> Command)
  | FunL Term Coterm


-- Commands

data Command = Term :|: Coterm
