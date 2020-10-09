{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Core.Expr
( Expr(..)
, QExpr(..)
) where

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

infixl 9 :$
infixl 7 :*

instance Scoped Expr where
  fvs = fvsDefault

instance Scoped1 Expr where
  fvs1 =  \case
    Free  v  -> pure (Free v)
    Bound n  -> boundVar1 Bound n
    TLam n b -> TLam n <$> fvs1 b
    TApp f a -> TApp <$> fvs1 f <*> pure a
    Lam  p b -> uncurry Lam <$> bindN Bound p (fvs b) (fvs1 b)
    f :$ a   -> (:$) <$> fvs1 f <*> fvs1 a
    Unit     -> pure Unit
    l :* r   -> (:*) <$> fvs1 l <*> fvs1 r

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
