{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Type
( TName(..)
, Type(..)
, tglobal
, tbound
, (>~>)
, unForAll
, (-->)
, (.$)
, (.*)
, _Unit
, _Type
, dropAnn
, TypeF(..)
, fold
) where

import Control.Effect.Empty
import Data.String (IsString(..))
import Data.Text (Text)
import Facet.Name
import Facet.Syntax
import Prettyprinter (Pretty)
import Text.Parser.Position (Located(..), Span)

newtype TName = TName { getTName :: Text }
  deriving (Eq, IsString, Ord, Pretty, Show)

newtype Type = In { out :: TypeF Type }

instance Located Type where
  locate = fmap In . Ann

tglobal :: TName -> Type
tglobal = In . Free

tbound :: Name -> Type
tbound = In . Bound

(>~>) :: (Name ::: Type) -> Type -> Type
(>~>) = fmap In . (:=>)
infixr 1 >~>

unForAll :: Has Empty sig m => Type -> m (Name ::: Type, Type)
unForAll t = case out t of
  t :=> b -> pure (t, b)
  _       -> empty

(-->) :: Type -> Type -> Type
(-->) = fmap In . (:->)
infixr 2 -->

(.$) = fmap In . (:$)
(.$) :: Type -> Type -> Type

infixl 9 .$


(.*) :: Type -> Type -> Type
(.*) = fmap In . (:*)
infixl 7 .*
-- FIXME: tupling/unit should take a list of types

_Unit :: Type
_Unit = In Unit

_Type :: Type
_Type = In Type


dropAnn :: Type -> Type
dropAnn e = case out e of
  Ann _ e -> e
  _       -> e


data TypeF t
  = Free TName
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


fold :: (TypeF a -> a) -> Type -> a
fold alg = go
  where
  go = alg . fmap go . out
