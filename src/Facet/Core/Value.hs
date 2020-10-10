{-# LANGUAGE TypeOperators #-}
module Facet.Core.Value
( Value(..)
) where

import Facet.Name
import Facet.Stack
import Facet.Syntax

data Value f a
  = Type
  | Void
  | Unit
  | (UName ::: Value f a) :=> (Value f a -> f (Value f a))
  | Either QName a :$ Stack (Value f a)
  | Value f a :-> Value f a
  | Value f a :*  Value f a

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*
