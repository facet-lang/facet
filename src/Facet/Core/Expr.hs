{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Core.Expr
( Expr(..)
, global_
, bound_
, tlam_
, tapp_
, lam_
, app_
, unit_
, prd_
, ExprF(..)
, fold
, OverTypes(..)
) where

import           Control.Category ((>>>))
import           Control.Lens (Prism', prism', review)
import qualified Facet.Core.Pattern as P
import           Facet.Core.Type (Type)
import           Facet.Name
import           Facet.Substitution as Subst
import           Facet.Vars

newtype Expr = In { out :: ExprF Expr }

instance Scoped Expr where
  fvs = fvsDefault

instance Scoped1 Expr where
  fvs1 = out >>> \case
    Free  v  -> pure (review global_ v)
    Bound n  -> bound1 (review bound_) n
    TLam n b -> curry (review tlam_) n <$> fvs1 b
    TApp f a -> curry (review tapp_) <$> fvs1 f <*> pure a
    Lam  p b -> review lam_ <$> bindN (review bound_) p b
    f :$ a   -> curry (review app_) <$> fvs1 f <*> fvs1 a
    Unit     -> pure (review unit_ ())
    l :* r   -> curry (review prd_) <$> fvs1 l <*> fvs1 r


global_ :: Prism' Expr QName
global_ = prism' (In . Free) (\case{ In (Free n) -> Just n ; _ -> Nothing })

bound_ :: Prism' Expr (Name E)
bound_ = prism' (In . Bound) (\case{ In (Bound n) -> Just n ; _ -> Nothing })


tlam_ :: Prism' Expr (Name T, Expr)
tlam_ = prism' (In . uncurry TLam) (\case{ In (TLam n b) -> Just (n, b) ; _ -> Nothing })

tapp_ :: Prism' Expr (Expr, Type)
tapp_ = prism' (In . uncurry TApp) (\case{ In (TApp f a) -> Just (f, a) ; _ -> Nothing })

lam_ :: Prism' Expr (P.Pattern (Name E), Expr)
lam_ = prism' (In . uncurry Lam) (\case{ In (Lam p b) -> Just (p, b) ; _ -> Nothing })

app_ :: Prism' Expr (Expr, Expr)
app_ = prism' (In . uncurry (:$)) (\case{ In (f :$ a) -> Just (f, a) ; _ -> Nothing })


unit_ :: Prism' Expr ()
unit_ = prism' (const (In Unit)) (\case{ In Unit -> Just () ; _ -> Nothing })

prd_ :: Prism' Expr (Expr, Expr)
prd_ = prism' (In . uncurry (:*)) (\case{ In (l :* r) -> Just (l, r) ; _ -> Nothing })


instance Substitutable Expr where
  subst sub = substitute sub . fvs1


data ExprF e
  = Free QName
  | Bound (Name E)
  | TLam (Name T) e
  | TApp e Type
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


newtype OverTypes = OverTypes { runOverTypes :: Expr }
