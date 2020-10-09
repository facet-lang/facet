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

data Expr
  = Free QName
  | Bound Level
  | TLam UName Expr
  | TApp Expr Type
  | Lam (P.Pattern UName) Expr
  | Expr :$ Expr
  | Unit
  | Expr :* Expr

infixl 9 :$
infixl 7 :*


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
    Bound n  -> QBound (levelToIndex d n)
    TLam n b -> QTLam n (go (incrLevel d) b)
    TApp f a -> QTApp (go d f) (T.quote' d a)
    Lam  p b -> QLam p (go (foldr (const incrLevel) d p) b)
    f :$ a   -> go d f :$$ go d a
    Unit     -> QUnit
    l :* r   -> go d l :** go d r
