{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Core.Expr
( Expr(..)
, QExpr(..)
, eval
, quote
) where

import           Control.Effect.Throw
import qualified Facet.Core.Pattern as P
import           Facet.Core.Type (QType, Type)
import qualified Facet.Core.Type as T
import           Facet.Error
import           Facet.Name
import           Facet.Pretty

data Expr f
  = Free QName
  | Bound Level
  | TLam UName (Type f Level -> f (Expr f))
  | TApp (Expr f) (Type f Level)
  | Lam (P.Pattern UName) ((Expr f) -> f (Expr f))
  | Expr f :$ Expr f
  | Unit
  | Expr f :* Expr f

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


-- FIXME: consider merging Type and Expr into a single datatype.
eval :: Has (Throw Err) sig m => [Either (Type m Level) (Expr m)] -> QExpr -> m (Expr m)
eval env = \case
  QFree  n  -> pure (Free n)
  QBound n  -> case env !! getIndex n of
    Right e -> pure e
    Left _T -> throwError $ Err (reflow "can’t use a type in an expression") []
  QTLam n b -> pure $ TLam n (\ v -> eval (Left v:env) b)
  QTApp f a -> TApp <$> eval env f <*> T.eval' (map (either pure (const (throwError (Err (reflow "can’t use an expression in a type") [])))) env) a
  QLam  p b -> pure $ Lam p (\ v -> eval (Right v:env) b)
  f :$$ a   -> (:$) <$> eval env f <*> eval env a
  QUnit     -> pure Unit
  l :** r   -> (:*) <$> eval env l <*> eval env r

quote :: Monad m => Expr m -> m QExpr
quote = go (Level 0)
  where
  go d = \case
    Free  v  -> pure $ QFree v
    Bound n  -> pure $ QBound (levelToIndex d n)
    TLam n b -> QTLam n <$> (go (incrLevel d) =<< b (T.bound d))
    TApp f a -> QTApp <$> go d f <*> (T.quote' d a)
    Lam  p b -> QLam p <$> (go (foldr (const incrLevel) d p) =<< b (Bound d))
    f :$ a   -> (:$$) <$> go d f <*> go d a
    Unit     -> pure QUnit
    l :* r   -> (:**) <$> go d l <*> go d r
