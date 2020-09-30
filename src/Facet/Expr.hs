module Facet.Expr
( Expr(..)
) where

import qualified Data.Text as T
import           Facet.Name

data Expr
  = Global T.Text
  | Bound Name
  | TLam Name Expr
  | Lam0 Name Expr
  | Expr :$ Expr

infixl 9 :$
