{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Type
( Type(..)
, TypeF(..)
, foldType
) where

import           Control.Effect.Parser.Span (Span)
import           Facet.Name
import qualified Facet.Surface as S
import           Facet.Syntax

newtype Type = In { out :: TypeF Type }

data TypeF t
  = Free S.TName
  | Bound Name
  | Type
  | Unit
  | (Name ::: t) :=> t
  | t :$ t
  | t :-> t
  | t :*  t
  | Ann Span t
  deriving (Foldable, Functor, Traversable)

infixr 1 :=>
infixl 9 :$
infixr 2 :->
infixl 7 :*

instance S.Type Type where
  tglobal = In . Free
  tbound = In . Bound

  (>~>) = fmap In . (:=>)

  (-->) = fmap In . (:->)

  (.$) = fmap In . (:$)

  (.*) = fmap In . (:*)

  _Unit = In Unit
  _Type = In Type

instance S.Located Type where
  locate = fmap In . Ann


foldType :: (TypeF a -> a) -> Type -> a
foldType alg = go
  where
  go = alg . fmap go . out
