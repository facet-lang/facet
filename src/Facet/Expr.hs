{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Expr
( Expr(..)
, interpret
, subst
) where

import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Text as T
import qualified Facet.Core as C
import qualified Facet.Core.HOAS as CH
import           Facet.Name
import qualified Facet.Type as Type

data Expr
  = Global T.Text
  | Bound Name
  | TLam FVs Name Expr
  | Lam0 FVs Name Expr
  | App FVs Expr Expr

instance Scoped Expr where
  maxBV = \case
    Global _   -> Nothing
    Bound _    -> Nothing
    TLam _ _ n -> maxBV n
    Lam0 _ _ n -> maxBV n
    App _ f a  -> maxBV f <> maxBV a

instance C.Expr Expr where
  global = Global
  bound = Bound
  tlam n b = TLam (IntSet.delete (id' n) (fvs b)) n b
  lam0 n b = Lam0 (IntSet.delete (id' n) (fvs b)) n b
  f $$ a = App (fvs f <> fvs a) f a

instance CH.Expr Type.Type Expr where
  tlam n b = n >>= \ n -> binderM C.tbound C.tlam n b
  lam0 n b = n >>= \ n -> binderM C.bound  C.lam0 n b

interpret :: C.Expr r => Expr -> r
interpret = \case
  Global n -> C.global n
  Bound n -> C.bound n
  TLam _ n b -> C.tlam n (interpret b)
  Lam0 _ n b -> C.lam0 n (interpret b)
  App _ f a -> interpret f C.$$ interpret a

subst :: IntMap.IntMap Expr -> Expr -> Expr
subst e = \case
  Global s -> Global s
  Bound n  -> (e IntMap.! id' n)
  TLam _ n b -> C.tlam' (hint n) (\ v -> subst (instantiate n v e) b)
  Lam0 _ n b -> C.lam0' (hint n) (\ v -> subst (instantiate n v e) b)
  App _ f a  -> subst e f C.$$ subst e a

fvs :: Expr -> FVs
fvs = \case
  Global _   -> IntSet.empty
  Bound  _   -> IntSet.empty
  TLam s _ _ -> s
  Lam0 s _ _ -> s
  App s _ _  -> s
