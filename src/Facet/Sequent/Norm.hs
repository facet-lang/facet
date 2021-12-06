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
import qualified Facet.Sequent.Class as Class
import           Facet.Syntax

-- Terms

data Term
  = Var (Var (LName Level))
  | MuR (Coterm -> Command)
  | FunR [(Pattern Name, Pattern (Name :=: Term) -> Term)]
  | ConR RName [Term]
  | StringR Text
  | DictR [RName :=: Term]
  | CompR [RName :=: Name] (Pattern (Name :=: Term) -> Term)


-- Coterms

data Coterm
  = Covar (Var (LName Level))
  | MuL (Term -> Command)
  | FunL Term Coterm


-- Commands

data Command = Term :|: Coterm


instance Class.Term Term Coterm Command where
  var = Var
  µR = MuR
  funR = FunR
  conR = ConR
  stringR = StringR
  dictR = DictR
  compR = CompR

  covar = Covar
  µL = MuL
  funL = FunL

  (|||) = (:|:)
