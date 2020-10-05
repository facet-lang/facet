{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
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
, unApp
, (.*)
, _Unit
, _Type
, dropAnn
, aeq
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

unApp :: Has Empty sig m => Type -> m (Type, Type)
unApp e = case out e of
  f :$ a -> pure (f, a)
  _      -> empty


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


aeq :: Type -> Type -> Bool
aeq = fold $ \ t1 t2 -> case (t1, out t2) of
  (Free  n1,           Free  n2)           -> n1 == n2
  (Bound n1,           Bound n2)           -> n1 == n2
  (Type,               Type)               -> True
  (Unit,               Unit)               -> True
  ((n1 ::: t1) :=> b1, (n2 ::: t2) :=> b2) -> n1 == n2 && t1 t2 && b1 b2
  (f1 :$ a1,           f2 :$ a2)           -> f1 f2 && a1 a2
  (a1 :-> b1,          a2 :-> b2)          -> a1 a2 && b1 b2
  (l1 :* r1,           l2 :* r2)           -> l1 l2 && r1 r2
  (Ann _ t1,           Ann _ t2)           -> t1 t2
  _                                        -> False


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
