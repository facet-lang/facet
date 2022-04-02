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
  = Var (Var (LName Index))
  | Lam [(Pattern Name, Term)]
  | App Term Term
  | Con QName [Term]
  | String Text
  | Dict [QName :=: Term]
  | Let (Pattern Name) Term Term
  | Comp [QName :=: Name] Term -- ^ NB: the first argument is a specialization of @'Pattern' 'Name'@ to the 'PDict' constructor
  deriving (Eq, Ord, Show)
