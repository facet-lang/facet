{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Core.Expr
( Expr(..)
, global_
, bound_
, tlam_
, lam_
, app_
, unit_
, prd_
, interpret
, subst
, ExprF(..)
, fold
) where

import           Control.Category ((>>>))
import           Control.Lens.Prism (Prism', prism')
import           Data.Coerce (coerce)
import qualified Facet.Core as C
import qualified Facet.Core.Pattern as P
import           Facet.Name
import           Facet.Vars

newtype Expr = In { out :: ExprF Expr }

instance Scoped Expr where
  fvs = out >>> \case
    Free _   -> mempty
    Bound  n -> fvs n
    TLam n b -> bind n (fvs b)
    Lam p b  -> foldr bind (fvs b) p
    f :$ a   -> fvs f <> fvs a
    Unit     -> mempty
    l :* r   -> fvs l <> fvs r

instance C.Expr Expr where
  global = In . Free
  bound = In . Bound
  tlam = fmap In . TLam
  lam = fmap In . Lam
  ($$) = fmap In . (:$)
  unit = In Unit
  (**) = fmap In . (:*)


global_ :: Prism' Expr QName
global_ = prism' (In . Free) (\case{ In (Free n) -> Just n ; _ -> Nothing })

bound_ :: Prism' Expr (Name E)
bound_ = prism' (In . Bound) (\case{ In (Bound n) -> Just n ; _ -> Nothing })


tlam_ :: Prism' Expr (Name T, Expr)
tlam_ = prism' (uncurry C.tlam) (\case{ In (TLam n b) -> Just (n, b) ; _ -> Nothing })

lam_ :: Prism' Expr (P.Pattern (Name E), Expr)
lam_ = prism' (uncurry C.lam) (\case{ In (Lam p b) -> Just (p, b) ; _ -> Nothing })

app_ :: Prism' Expr (Expr, Expr)
app_ = prism' (uncurry (C.$$)) (\case{ In (f :$ a) -> Just (f, a) ; _ -> Nothing })


unit_ :: Prism' Expr ()
unit_ = prism' (const (In Unit)) (\case{ In Unit -> Just () ; _ -> Nothing })

prd_ :: Prism' Expr (Expr, Expr)
prd_ = prism' (In . uncurry (:*)) (\case{ In (l :* r) -> Just (l, r) ; _ -> Nothing })


interpret :: C.Expr r => Expr -> r
interpret = out >>> \case
  Free n -> C.global n
  Bound n -> C.bound n
  TLam n b -> C.tlam n (interpret b)
  Lam n b -> C.lam n (interpret b)
  f :$ a -> interpret f C.$$ interpret a
  Unit -> C.unit
  l :* r -> interpret l C.** interpret r

-- FIXME: this is pretty inefficient for multiple renamings; we should try to fuse renamings.
rename :: Name a -> Name a -> Expr -> Expr
rename x y = go
  where
  go = out >>> \case
    Free s        -> C.global s
    Bound z
      | x `eqN` z -> C.bound (coerce y)
      | otherwise -> C.bound z
    TLam z b
      | z `eqN` x -> C.tlam z b
      | otherwise -> C.tlam z (go b)
    Lam z b
      | elemN x z -> C.lam z b
      | otherwise -> C.lam z (go b)
    f :$ a        -> go f C.$$ go a
    Unit          -> C.unit
    l :* r        -> go l C.** go r

-- FIXME: this is pretty inefficient for multiple substitutions; we should try to fuse substitutions.
subst :: Name a -> Expr -> Expr -> Expr
subst x e = go
  where
  go = out >>> \case
    Free s        -> C.global s
    Bound n
      | n `eqN` x -> e
      | otherwise -> C.bound n
    TLam n b      ->
      let n' = prime (hint n) (fvs b <> fvs e)
          b' = go (rename n n' b)
      in C.tlam n' b'
    Lam p b       ->
      let vs = fvs b <> fvs e
          (re, p') = renameAccumL (\ i f n -> let n' = Name (hint n) i in (f . rename n n', n')) vs id p
          b' = go (re b)
      in C.lam p' b'
    f :$ a        -> go f C.$$ go a
    Unit          -> C.unit
    l :* r        -> go l C.** go r


data ExprF e
  = Free QName
  | Bound (Name E)
  | TLam (Name T) e
  | Lam (P.Pattern (Name E)) e
  | e :$ e
  | Unit
  | e :* e
  deriving (Foldable, Functor, Show, Traversable)

infixl 9 :$
infixl 7 :*

fold :: (ExprF a -> a) -> Expr -> a
fold alg = go
  where
  go = alg . fmap go . out
