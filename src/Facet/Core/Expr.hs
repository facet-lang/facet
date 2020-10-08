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
, subst
, ExprF(..)
, fold
) where

import           Control.Category ((>>>))
import           Control.Lens (Prism', prism', review)
import           Data.Coerce (coerce)
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


global_ :: Prism' Expr QName
global_ = prism' (In . Free) (\case{ In (Free n) -> Just n ; _ -> Nothing })

bound_ :: Prism' Expr (Name E)
bound_ = prism' (In . Bound) (\case{ In (Bound n) -> Just n ; _ -> Nothing })


tlam_ :: Prism' Expr (Name T, Expr)
tlam_ = prism' (In . uncurry TLam) (\case{ In (TLam n b) -> Just (n, b) ; _ -> Nothing })

lam_ :: Prism' Expr (P.Pattern (Name E), Expr)
lam_ = prism' (In . uncurry Lam) (\case{ In (Lam p b) -> Just (p, b) ; _ -> Nothing })

app_ :: Prism' Expr (Expr, Expr)
app_ = prism' (In . uncurry (:$)) (\case{ In (f :$ a) -> Just (f, a) ; _ -> Nothing })


unit_ :: Prism' Expr ()
unit_ = prism' (const (In Unit)) (\case{ In Unit -> Just () ; _ -> Nothing })

prd_ :: Prism' Expr (Expr, Expr)
prd_ = prism' (In . uncurry (:*)) (\case{ In (l :* r) -> Just (l, r) ; _ -> Nothing })


-- FIXME: this is pretty inefficient for multiple renamings; we should try to fuse renamings.
rename :: Name a -> Name a -> Expr -> Expr
rename x y = go
  where
  go = out >>> \case
    Free s        -> review global_ s
    Bound z
      | x `eqN` z -> review bound_ (coerce y)
      | otherwise -> review bound_ z
    TLam z b
      | z `eqN` x -> review tlam_ (z, b)
      | otherwise -> review tlam_ (z, go b)
    Lam z b
      | elemN x z -> review lam_ (z, b)
      | otherwise -> review lam_ (z, go b)
    f :$ a        -> review app_ (go f, go a)
    Unit          -> review unit_ ()
    l :* r        -> review prd_ (go l, go r)

-- FIXME: this is pretty inefficient for multiple substitutions; we should try to fuse substitutions.
subst :: Name a -> Expr -> Expr -> Expr
subst x e = go
  where
  go = out >>> \case
    Free s        -> review global_ s
    Bound n
      | n `eqN` x -> e
      | otherwise -> review bound_ n
    TLam n b      ->
      let n' = prime (hint n) (fvs b <> fvs e)
          b' = go (rename n n' b)
      in review tlam_ (n', b')
    Lam p b       ->
      let vs = fvs b <> fvs e
          (re, p') = renameAccumL (\ i f n -> let n' = Name (hint n) i in (f . rename n n', n')) vs id p
          b' = go (re b)
      in review lam_ (p', b')
    f :$ a        -> review app_ (go f, go a)
    Unit          -> review unit_ ()
    l :* r        -> review prd_ (go l, go r)


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
