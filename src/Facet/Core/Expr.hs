{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Core.Expr
( Expr(..)
, QExpr(..)
, quote
) where

import qualified Facet.Core.Pattern as P
import           Facet.Core.Type (QType, Type)
import qualified Facet.Core.Type as T
import           Facet.Name
import           Facet.Substitution as Subst
import           Facet.Vars

data Expr
  = Free QName
  | Bound (Name E)
  | TLam UName Expr
  | TApp Expr Type
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


quote :: Expr -> QExpr
quote = go (Level 0)
  where
  go d = \case
    Free  v  -> QFree v
    Bound n  -> QBound (levelToIndex d (Level (id' n)))
    TLam n b -> QTLam n (go (incrLevel d) b)
    TApp f a -> QTApp (go d f) (T.quote' d a)
    Lam  p b -> QLam (hint <$> p) (go (incrLevel d) b) -- FIXME: incr once for each variable bound in the pattern
    f :$ a   -> go d f :$$ go d a
    Unit     -> QUnit
    l :* r   -> go d l :** go d r
