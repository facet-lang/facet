{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Expr
( Expr(..)
) where

import           Control.Applicative (liftA2)
import qualified Data.Text as T
import qualified Facet.Core as C
import qualified Facet.Core.HOAS as CH
import           Facet.Name
import qualified Facet.Type as Type

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

instance CH.Expr Type.Type Expr where
  global = pure . C.global
  tlam n b = n >>= \ n -> binderM C.tbound TLam n b
  lam0 n b = n >>= \ n -> binderM C.bound  Lam0 n b
  ($$) = liftA2 (C.$$)
