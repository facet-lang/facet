{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Value
( Value(..)
, global
, bound
, unArrow
) where

import Control.Effect.Empty
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
  | Value f a :*  Value f a

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*


global :: QName -> Value f a
global n = Left n :$ Nil

bound :: a -> Value f a
bound n = Right n :$ Nil


unArrow :: Has Empty sig m => Value f a -> m (Value f a, Value f a)
unArrow = \case{ a :-> b -> pure (a, b) ; _ -> empty }
