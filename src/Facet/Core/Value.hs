{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Value
( Value(..)
, global
, bound
, unForAll
, unArrow
, unProductT
, ($$)
, ($$*)
) where

import Control.Effect.Empty
import Data.Foldable (foldl')
import Facet.Core.Pattern
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
  | Lam (Pattern UName) (Pattern (Value f a) -> f (Value f a))
  | Either QName a :$ Stack (Value f a)
  | TPrd (Value f a) (Value f a)
  | Prd (Value f a) (Value f a)

infixr 0 :=>
infixl 9 :$
infixr 0 :->


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


($$) :: Applicative f => Value f Level -> Value f Level -> f (Value f Level)
(f :$ as) $$ a = pure (f :$ (as :> a))
(_ :=> b) $$ a = b a
_         $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: (Foldable t, Monad f) => Value f Level -> t (Value f Level) -> f (Value f Level)
f $$* as = foldl' (\ f a -> f >>= ($$ a)) (pure f) as

infixl 9 $$, $$*
