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
, QExpr(..)
) where

import           Control.Lens (Prism', prism', review)
import qualified Facet.Core.Pattern as P
import           Facet.Core.Type (QType)
import           Facet.Name
import           Facet.Substitution as Subst
import           Facet.Vars

data Expr
  = Free QName
  | Bound (Name E)
  | TLam UName Expr
  | TApp Expr QType
  | Lam (P.Pattern (Name E)) Expr
  | Expr :$ Expr
  | Unit
  | Expr :* Expr

instance Scoped Expr where
  fvs = fvsDefault

instance Scoped1 Expr where
  fvs1 =  \case
    Free  v  -> pure (review global_ v)
    Bound n  -> boundVar1 (review bound_) n
    TLam n b -> curry (review tlam_) n <$> fvs1 b
    TApp f a -> curry (review tapp_) <$> fvs1 f <*> pure a
    Lam  p b -> review lam_ <$> bindN (review bound_) p (fvs b) (fvs1 b)
    f :$ a   -> curry (review app_) <$> fvs1 f <*> fvs1 a
    Unit     -> pure (review unit_ ())
    l :* r   -> curry (review prd_) <$> fvs1 l <*> fvs1 r


global_ :: Prism' Expr QName
global_ = prism' Free (\case{ Free n -> Just n ; _ -> Nothing })

bound_ :: Prism' Expr (Name E)
bound_ = prism' Bound (\case{ Bound n -> Just n ; _ -> Nothing })


tlam_ :: Prism' Expr (UName, Expr)
tlam_ = prism' (uncurry TLam) (\case{ TLam n b -> Just (n, b) ; _ -> Nothing })

tapp_ :: Prism' Expr (Expr, QType)
tapp_ = prism' (uncurry TApp) (\case{ TApp f a -> Just (f, a) ; _ -> Nothing })

lam_ :: Prism' Expr (P.Pattern (Name E), Expr)
lam_ = prism' (uncurry Lam) (\case{ Lam p b -> Just (p, b) ; _ -> Nothing })

app_ :: Prism' Expr (Expr, Expr)
app_ = prism' (uncurry (:$)) (\case{ f :$ a -> Just (f, a) ; _ -> Nothing })


unit_ :: Prism' Expr ()
unit_ = prism' (const Unit) (\case{ Unit -> Just () ; _ -> Nothing })

prd_ :: Prism' Expr (Expr, Expr)
prd_ = prism' (uncurry (:*)) (\case{ l :* r -> Just (l, r) ; _ -> Nothing })


instance Substitutable Expr where
  subst sub = substitute sub . fvs1


data QExpr
  = QFree QName
  | QBound Index
  | QTLam UName QExpr
  | QTApp QExpr QType
  | QLam (P.Pattern UName) QExpr
  | QExpr :$$ QExpr
  | QUnit
  | QExpr :** QExpr
  deriving (Show)

infixl 9 :$$
infixl 7 :**
