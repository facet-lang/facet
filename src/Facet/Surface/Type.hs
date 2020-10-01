{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Type
( Type(..)
) where

import           Facet.Name
import qualified Facet.Surface as S
import           Facet.Syntax

data Type
  = Free S.TName
  | Bound Name
  | Type
  | Unit
  | (Name ::: Type) :=> Type
  | Type :$ Type
  | Type :-> Type
  | Type :*  Type

infixr 1 :=>
infixl 9 :$
infixr 2 :->
infixl 7 :*

instance S.Type Type where
  tglobal = Free
  tbound = Bound

  (>~>) = (:=>)

  (-->) = (:->)

  (.$) = (:$)

  (.*) = (:*)

  _Unit = Unit
  _Type = Type
