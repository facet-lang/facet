{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Expr
( Expr(..)
, interpret
, subst
) where

import qualified Data.IntMap as IntMap
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
  tlam n b = n >>= \ n -> binderM C.tbound TLam n b
  lam0 n b = n >>= \ n -> binderM C.bound  Lam0 n b

interpret :: C.Expr r => Expr -> r
interpret = \case
  Global n -> C.global n
  Bound n -> C.bound n
  TLam n b -> C.tlam n (interpret b)
  Lam0 n b -> C.lam0 n (interpret b)
  f :$ a -> interpret f C.$$ interpret a

subst :: IntMap.IntMap Expr -> Expr -> Expr
subst e = \case
  Global s -> Global s
  Bound n  -> (e IntMap.! id' n)
  TLam n b -> C.tlam' (hint n) (\ v -> subst (instantiate n v e) b)
  Lam0 n b -> C.lam0' (hint n) (\ v -> subst (instantiate n v e) b)
  f :$ a   -> subst e f :$ subst e a
