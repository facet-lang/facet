module Facet.Term.Expr
( -- * Term expressions
  Term(..)
) where

import Data.Text (Text)
import Facet.Name
import Facet.Syntax
import Facet.Syntax.Pattern

-- Term expressions

data Term
  = Var (Var (LName Index))
  | Lam [(Pattern Name, Term)]
  | App Term Term
  | Con RName [Term]
  | String Text
  | Dict [RName :=: Term]
  | Let (Pattern Name) Term Term
  | Comp [RName :=: Name] Term -- ^ NB: the first argument is a specialization of @'Pattern' 'Name'@ to the 'PDict' constructor
  deriving (Eq, Ord, Show)
