{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
module Facet.Core.Type
( Type(..)
, global
, bound
, unForAll
, unArrow
, unProduct
, (.$)
, (.$*)
, QType(..)
, unQApp
, eval
, quote
, quote'
) where

import Control.Effect.Empty
import Data.Foldable (foldl')
import Facet.Error
import Facet.Name
import Facet.Stack
import Facet.Syntax

-- FIXME: computation types
-- FIXME: effect signatures
data Type
  = Type
  | Void
  | Unit
  | (UName ::: Type) :=> (Type -> Either Err Type)
  | Either QName Level :$ Stack (Type)
  | Type :-> Type
  | Type :*  Type

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*


global :: QName -> Type
global n = Left n :$ Nil

bound :: Level -> Type
bound n = Right n :$ Nil


unForAll :: Has Empty sig m => Type -> m (UName ::: Type, Type -> Either Err Type)
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unArrow :: Has Empty sig m => Type -> m (Type, Type)
unArrow = \case{ a :-> b -> pure (a, b) ; _ -> empty }

unProduct :: Has Empty sig m => Type -> m (Type, Type)
unProduct = \case{ l :* r -> pure (l, r) ; _ -> empty }


(.$) :: Type -> Type -> Either Err Type
(f :$ as) .$ a = pure (f :$ (as :> a))
(_ :=> b) .$ a = b a
_         .$ _ = error "can’t apply non-neutral/forall type"

(.$*) :: Foldable t => Type -> t Type -> Either Err Type
f .$* as = foldl' (\ f a -> f >>= \ f' -> f' .$ a) (Right f) as

infixl 9 .$, .$*


data QType
  = QFree QName
  | QBound Index
  | QType
  | QVoid
  | QUnit
  | (UName ::: QType) :==> QType
  | QType :$$ QType
  | QType :--> QType
  | QType :**  QType
  deriving (Eq, Ord, Show)

infixr 0 :==>
infixl 9 :$$
infixr 0 :-->
infixl 7 :**

unQApp :: Has Empty sig m => QType -> m (QType, QType)
unQApp = \case{ f :$$ a -> pure (f, a) ; _ -> empty }


eval :: [Type] -> QType -> Either Err Type
eval env = \case
  QFree n  -> pure (global n)
  QBound n -> pure (env !! getIndex n)
  QType    -> pure Type
  QVoid    -> pure Void
  QUnit    -> pure Unit
  t :==> b -> do
    t' <- traverse (eval env) t
    pure (t' :=> \ v -> eval (v:env) b)
  f :$$  a -> do
    f' <- eval env f
    a' <- eval env a
    f' .$ a'
  a :--> b -> (:->) <$> eval env a <*> eval env b
  l :**  r -> (:*)  <$> eval env l <*> eval env r

quote :: Type -> Either Err QType
quote = quote' (Level 0)

quote' :: Level -> Type -> Either Err QType
quote' n = \case
  Type    -> pure QType
  Void    -> pure QVoid
  Unit    -> pure QUnit
  t :=> b -> do
    t' <- traverse (quote' n) t
    b' <- b (bound n)
    (t' :==>) <$> quote' (incrLevel n) b'
  f :$ as -> foldl' (:$$) (either QFree (QBound . levelToIndex n) f) <$> traverse (quote' n) as
  a :-> b -> (:-->) <$> quote' n a <*> quote' n b
  l :*  r -> (:**)  <$> quote' n l <*> quote' n r
