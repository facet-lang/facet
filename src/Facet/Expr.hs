{-# LANGUAGE LambdaCase #-}
module Facet.Expr
( Expr(..)
) where

import qualified Data.Text as T
import qualified Facet.Core as C
import           Facet.Name

data Expr
  = Global T.Text
  | Bound Name
  | TLam Name Expr
  | Lam0 Name Expr
  | Expr :$ Expr

infixl 9 :$

instance Scoped Expr where
  maxBV = \case
    Global _ -> Nothing
    Bound _  -> Nothing
    TLam n _ -> maxBV n
    Lam0 n _ -> maxBV n
    f :$ a   -> maxBV f <> maxBV a

instance C.Expr Expr where
  global = Global
  bound = Bound
  tlam = TLam
  lam0 = Lam0
  ($$) = (:$)
