{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Type
( Type(..)
) where

import Data.Text (Text)
import Facet.Name
import Facet.Syntax

data Type
  = Free Text
  | Bound Name
  | Type
  | Unit
  | (Name ::: Type) :=> Type
  | Type :$ Type
  | Type :-> Type
  | Type :*  Type

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*
