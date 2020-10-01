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
  fvs = \case
    Global _   -> IntSet.empty
    Bound  n   -> fvs n
    TLam s _ _ -> s
    Lam0 s _ _ -> s
    App s _ _  -> s

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

rename :: Name -> Name -> Expr -> Expr
rename x y = go
  where
  go = \case
    Global s      -> Global s
    Bound z
      | x == z    -> Bound y
      | otherwise -> Bound z
    TLam s z b
      | z == x    -> TLam s z b
      | otherwise -> C.tlam z (go b)
    Lam0 s z b
      | z == x    -> Lam0 s z b
      | otherwise -> C.lam0 z (go b)
    App _ f a     -> go f C.$$ go a

subst :: IntMap.IntMap Expr -> Expr -> Expr
subst e = \case
  Global s -> Global s
  Bound n  -> (e IntMap.! id' n)
  TLam _ n b -> C.tlam' (hint n) (\ v -> subst (instantiate n v e) b)
  Lam0 _ n b -> C.lam0' (hint n) (\ v -> subst (instantiate n v e) b)
  App _ f a  -> subst e f C.$$ subst e a
