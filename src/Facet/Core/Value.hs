{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Value
( Value(..)
, Type
, Expr
, global
, bound
, unForAll
, unArrow
, unProductT
, ($$)
, ($$*)
, close
, closeAll
) where

import Control.Effect.Empty
import Data.Foldable (foldl')
import Facet.Name
import Facet.Stack
import Facet.Syntax

data Value f a
  = Type
  | Void
  | UnitT
  | Unit
  | (UName ::: Value f a) :=> (Value f a -> f (Value f a))
  | TLam UName (Value f a -> f (Value f a))
  | Value f a :-> Value f a
  | Lam UName (Value f a -> f (Value f a))
  | Either QName a :$ Stack (Value f a)
  | TPrd (Value f a) (Value f a)
  | Prd (Value f a) (Value f a)

infixr 0 :=>
infixl 9 :$
infixr 0 :->


type Type = Value
type Expr = Value


global :: QName -> Value f a
global n = Left n :$ Nil

bound :: a -> Value f a
bound n = Right n :$ Nil


unForAll :: Has Empty sig m => Value f a -> m (UName ::: Value f a, Value f a -> f (Value f a))
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unArrow :: Has Empty sig m => Value f a -> m (Value f a, Value f a)
unArrow = \case{ a :-> b -> pure (a, b) ; _ -> empty }

unProductT :: Has Empty sig m => Value f a -> m (Value f a, Value f a)
unProductT = \case{ TPrd l r -> pure (l, r) ; _ -> empty }


($$) :: Applicative f => Value f a -> Value f a -> f (Value f a)
(f :$ as) $$ a = pure (f :$ (as :> a))
(_ :=> b) $$ a = b a
TLam _ b  $$ a = b a
Lam  _ b  $$ a = b a
_         $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (Foldable t, Monad f) => Value f a -> t (Value f a) -> f (Value f a)
f $$* as = foldl' (\ f a -> f >>= ($$ a)) (pure f) as

infixl 9 $$, $$*


close :: Monad m => Stack (Value m a) -> Value m Level -> m (Value m a)
close env = \case
  Type     -> pure Type
  Void     -> pure Void
  UnitT    -> pure UnitT
  Unit     -> pure Unit
  t :=> b  -> do
    t' <- traverse (close env) t
    pure $ t' :=> \ v -> close (env:>v) =<< b (bound (Level (length env)))
  a :-> b  -> (:->) <$> close env a <*> close env b
  TLam n b -> pure $ TLam n $ \ v -> close (env:>v) =<< b (bound (Level (length env)))
  Lam  n b -> pure $ Lam  n $ \ v -> close (env:>v) =<< b (bound (Level (length env)))
  f :$ as  -> do
    let f' = either global ((env !) . getIndex . levelToIndex (Level (length env))) f
    as' <- traverse (close env) as
    f' $$* as'
  TPrd l r -> TPrd <$> close env l <*> close env r
  Prd l r  -> Prd  <$> close env l <*> close env r

closeAll :: Monad m => Stack (Value m Level) -> m (Stack (Value m a))
closeAll = \case
  Nil     -> pure Nil
  as :> a -> do
    as' <- closeAll as
    a'  <- close as' a
    pure $ as' :> a'
