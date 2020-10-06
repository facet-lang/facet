{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Core.Expr
( Expr(..)
, app_
, interpret
, subst
, ExprF(..)
, fold
) where

import           Control.Category ((>>>))
import           Control.Lens.Prism
import qualified Data.IntSet as IntSet
import qualified Facet.Core as C
import           Facet.Name

newtype Expr = In { out :: ExprF Expr }

instance Scoped Expr where
  fvs = out >>> \case
    Global _   -> IntSet.empty
    Bound  n   -> fvs n
    TLam s _ _ -> s
    Lam s _ _  -> s
    App s _ _  -> s
    Unit       -> IntSet.empty
    Pair s _ _ -> s

instance C.Expr Expr where
  global = In . Global
  bound = In . Bound
  tlam n b = In $ TLam (IntSet.delete (id' n) (fvs b)) n b
  lam n b = In $ Lam (IntSet.delete (id' n) (fvs b)) n b
  f $$ a = In $ App (fvs f <> fvs a) f a
  unit = In Unit
  l ** r = In $ Pair (fvs l <> fvs r) l r

app_ :: Prism' Expr (Expr, Expr)
app_ = prism' (uncurry (C.$$)) (\case{ In (App _ f a) -> Just (f, a) ; _ -> Nothing })

interpret :: C.Expr r => Expr -> r
interpret = out >>> \case
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
  go = out >>> \case
    Global s      -> C.global s
    Bound z
      | x == z    -> C.bound y
      | otherwise -> C.bound z
    TLam s z b
      | z == x    -> In $ TLam s z b
      | otherwise -> C.tlam z (go b)
    Lam s z b
      | z == x    -> In $ Lam s z b
      | otherwise -> C.lam z (go b)
    App _ f a     -> go f C.$$ go a
    Unit          -> C.unit
    Pair _ l r    -> go l C.** go r

subst :: Name -> Expr -> Expr -> Expr
subst x e = go
  where
  go = out >>> \case
    Global s      -> C.global s
    Bound n
      | n == x    -> e
      | otherwise -> C.bound n
    TLam _ n b    -> let n' = prime (hint n) (fvs b <> fvs e)
                         b' = go (rename n n' b)
                     in C.tlam n' b'
    Lam _ n b     -> let n' = prime (hint n) (fvs b <> fvs e)
                         b' = go (rename n n' b)
                     in C.lam n' b'
    App _ f a     -> go f C.$$ go a
    Unit          -> C.unit
    Pair _ l r    -> go l C.** go r


data ExprF e
  = Global QName
  | Bound Name
  | TLam FVs Name e
  | Lam FVs Name e
  | App FVs e e
  | Unit
  | Pair FVs e e
  deriving (Foldable, Functor, Show, Traversable)

fold :: (ExprF a -> a) -> Expr -> a
fold alg = go
  where
  go = alg . fmap go . out
