{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Expr
( Expr(..)
, interpret
, subst
) where

import           Control.Lens.Prism
import qualified Data.IntSet as IntSet
import qualified Facet.Core as C
import           Facet.Name

data Expr
  = Global QName
  | Bound Name
  | TLam FVs Name Expr
  | Lam FVs Name Expr
  | App FVs Expr Expr
  | Unit
  | Pair FVs Expr Expr
  deriving (Show)

instance Scoped Expr where
  fvs = \case
    Global _   -> IntSet.empty
    Bound  n   -> fvs n
    TLam s _ _ -> s
    Lam s _ _  -> s
    App s _ _  -> s
    Unit       -> IntSet.empty
    Pair s _ _ -> s

instance C.Expr Expr where
  global = Global
  bound = Bound
  tlam n b = TLam (IntSet.delete (id' n) (fvs b)) n b
  lam n b = Lam (IntSet.delete (id' n) (fvs b)) n b
  f $$ a = App (fvs f <> fvs a) f a
  unit = Unit
  l ** r = Pair (fvs l <> fvs r) l r

_App :: Prism' Expr (Expr, Expr)
_App = prism' (uncurry (C.$$)) (\case{ App _ f a -> Just (f, a) ; _ -> Nothing })

interpret :: C.Expr r => Expr -> r
interpret = \case
  Global n -> C.global n
  Bound n -> C.bound n
  TLam _ n b -> C.tlam n (interpret b)
  Lam _ n b -> C.lam n (interpret b)
  App _ f a -> interpret f C.$$ interpret a
  Unit -> C.unit
  Pair _ l r -> interpret l C.** interpret r

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
    Lam s z b
      | z == x    -> Lam s z b
      | otherwise -> C.lam z (go b)
    App _ f a     -> go f C.$$ go a
    Unit          -> Unit
    Pair _ l r    -> go l C.** go r

subst :: Name -> Expr -> Expr -> Expr
subst x e = go
  where
  go = \case
    Global s      -> Global s
    Bound n
      | n == x    -> e
      | otherwise -> Bound n
    TLam _ n b    -> let n' = prime (hint n) (fvs b <> fvs e)
                         b' = go (rename n n' b)
                     in C.tlam n' b'
    Lam _ n b     -> let n' = prime (hint n) (fvs b <> fvs e)
                         b' = go (rename n n' b)
                     in C.lam n' b'
    App _ f a     -> go f C.$$ go a
    Unit          -> Unit
    Pair _ l r    -> go l C.** go r
