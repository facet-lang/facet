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
import qualified Facet.Core as C
import           Facet.Name
import           Facet.Vars

newtype Expr = In { out :: ExprF Expr }

instance Scoped Expr where
  fvs = out >>> \case
    Global _ -> mempty
    Bound  n -> fvs n
    TLam n b -> bind n (fvs b)
    Lam n b  -> bind n (fvs b)
    App f a  -> fvs f <> fvs a
    Unit     -> mempty
    Pair l r -> fvs l <> fvs r

instance C.Expr Expr where
  global = In . Global
  bound = In . Bound
  tlam = fmap In . TLam
  lam = fmap In . Lam
  ($$) = fmap In . App
  unit = In Unit
  (**) = fmap In . Pair

app_ :: Prism' Expr (Expr, Expr)
app_ = prism' (uncurry (C.$$)) (\case{ In (App f a) -> Just (f, a) ; _ -> Nothing })

interpret :: C.Expr r => Expr -> r
interpret = out >>> \case
  Global n -> C.global n
  Bound n -> C.bound n
  TLam n b -> C.tlam n (interpret b)
  Lam n b -> C.lam n (interpret b)
  App f a -> interpret f C.$$ interpret a
  Unit -> C.unit
  Pair l r -> interpret l C.** interpret r

rename :: Name -> Name -> Expr -> Expr
rename x y = go
  where
  go = out >>> \case
    Global s      -> C.global s
    Bound z
      | x == z    -> C.bound y
      | otherwise -> C.bound z
    TLam z b
      | z == x    -> C.tlam z b
      | otherwise -> C.tlam z (go b)
    Lam z b
      | z == x    -> C.lam z b
      | otherwise -> C.lam z (go b)
    App f a       -> go f C.$$ go a
    Unit          -> C.unit
    Pair l r      -> go l C.** go r

subst :: Name -> Expr -> Expr -> Expr
subst x e = go
  where
  go = out >>> \case
    Global s      -> C.global s
    Bound n
      | n == x    -> e
      | otherwise -> C.bound n
    TLam n b      -> let n' = prime (hint n) (fvs b <> fvs e)
                         b' = go (rename n n' b)
                     in C.tlam n' b'
    Lam n b       -> let n' = prime (hint n) (fvs b <> fvs e)
                         b' = go (rename n n' b)
                     in C.lam n' b'
    App f a       -> go f C.$$ go a
    Unit          -> C.unit
    Pair l r      -> go l C.** go r


data ExprF e
  = Global QName
  | Bound Name
  | TLam Name e
  | Lam Name e
  | App e e
  | Unit
  | Pair e e
  deriving (Foldable, Functor, Show, Traversable)

fold :: (ExprF a -> a) -> Expr -> a
fold alg = go
  where
  go = alg . fmap go . out
