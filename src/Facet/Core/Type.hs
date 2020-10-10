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
, eval'
, quote
, quote'
) where

import Control.Effect.Empty
import Control.Effect.Error
import Data.Foldable (foldl')
import Facet.Error
import Facet.Name
import Facet.Pretty
import Facet.Stack
import Facet.Syntax
import Prettyprinter (pretty)

-- FIXME: computation types
-- FIXME: effect signatures
-- FIXME: do we need quotation? if we did the PHOAS thing we could interpret using free variables of whatever shape rather than forcing every interpreter to carry a context/use de bruijn indices, at the cost of making it harder to take the type apart for one purpose and put it back together for another.
data Type f
  = Type
  | Void
  | Unit
  | (UName ::: Type f) :=> (Type f -> f (Type f))
  | Either QName Level :$ Stack (Type f)
  | Type f :-> Type f
  | Type f :*  Type f

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*


global :: QName -> Type f
global n = Left n :$ Nil

bound :: Level -> Type f
bound n = Right n :$ Nil


unForAll :: Has Empty sig m => Type f -> m (UName ::: Type f, Type f -> f (Type f))
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unArrow :: Has Empty sig m => Type f -> m (Type f, Type f)
unArrow = \case{ a :-> b -> pure (a, b) ; _ -> empty }

unProduct :: Has Empty sig m => Type f -> m (Type f, Type f)
unProduct = \case{ l :* r -> pure (l, r) ; _ -> empty }


(.$) :: Has (Throw Err) sig f => Type f -> Type f -> f (Type f)
(f :$ as) .$ a = pure (f :$ (as :> a))
(_ :=> b) .$ a = b a
f         .$ a = do
  f' <- quote f
  a' <- quote a
  -- FIXME: prettyprint the types.
  -- FIXME: we probably require some sort of context to print them in?
  throwError $ Err (reflow "can’t apply non-neutral/forall type") [pretty (show f'), pretty (show a')]

(.$*) :: (Foldable t, Has (Throw Err) sig f) => Type f -> t (Type f) -> f (Type f)
f .$* as = foldl' (\ f a -> f >>= \ f' -> f' .$ a) (pure f) as

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


eval :: Has (Throw Err) sig m => [Type m] -> QType -> m (Type m)
eval = eval' . map pure

eval' :: Has (Throw Err) sig m => [m (Type m)] -> QType -> m (Type m)
eval' env = \case
  QFree n  -> pure (global n)
  QBound n -> env !! getIndex n
  QType    -> pure Type
  QVoid    -> pure Void
  QUnit    -> pure Unit
  t :==> b -> do
    t' <- traverse (eval' env) t
    pure (t' :=> \ v -> eval' (pure v:env) b)
  f :$$  a -> do
    f' <- eval' env f
    a' <- eval' env a
    f' .$ a'
  a :--> b -> (:->) <$> eval' env a <*> eval' env b
  l :**  r -> (:*)  <$> eval' env l <*> eval' env r

quote :: Monad m => Type m -> m QType
quote = quote' (Level 0)

quote' :: Monad m => Level -> Type m -> m QType
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
