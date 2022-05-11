module Facet.Term.Expr
( -- * Term expressions
  Term(..)
) where

import Data.Text (Text)
import Facet.Name
import Facet.Pattern
import Facet.Syntax

-- Term expressions

data Term
  = Var (Var Index)
  | Lam [(Pattern Name, Term)]
  | App Term Term
  | Con QName [Term]
  | String Text
  | Let (Pattern Name) Term Term
  deriving (Eq, Ord, Show)
