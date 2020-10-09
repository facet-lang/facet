{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
module Facet.Core.Type
( Type(..)
, global
, Facet.Core.Type.bound
, unForAll
, unArrow
, unProduct
, (.$)
, (.$*)
, TypeF(..)
, fold
, unfold
, QType(..)
) where

import Control.Effect.Empty
import Data.Foldable (foldl')
import Facet.Name
import Facet.Stack
import Facet.Substitution as Subst hiding (empty)
import Facet.Syntax
import Facet.Vars

data Type
  = Type
  | Void
  | Unit
  | (Name T ::: Type) :=> Type
  | Either (Name T) QName :$ Stack Type
  | Type :-> Type
  | Type :*  Type
  deriving (Show)

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*

instance Scoped Type where
  fvs = fvsDefault

instance Scoped1 Type where
  fvs1 = \case
    Type    -> pure Type
    Void    -> pure Void
    Unit    -> pure Unit
    t :=> b -> mk <$> fvs1 (ty t) <*> bind1 bound (tm t) (fvs b) (fvs1 b)
      where
      mk t' (n', b') = n' ::: t' :=> b'
    f :$ as -> f' <*> traverse fvs1 as
      where
      f' = case f of
        Left f -> (.$*) <$> boundVar1 bound f
        _      -> pure (f :$)
    a :-> b -> (:->) <$> fvs1 a <*> fvs1 b
    l :*  r -> (:*)  <$> fvs1 l <*> fvs1 r


out :: Type -> TypeF Type
out = \case
  Type    -> TypeF
  Void    -> VoidF
  Unit    -> UnitF
  f :$ as -> f :$$ as
  t :=> b -> t :==> b
  a :-> b -> a :--> b
  l :*  r -> l :**  r

inn :: TypeF Type -> Type
inn = \case
  TypeF    -> Type
  VoidF    -> Void
  UnitF    -> Unit
  f :$$ as -> f :$ as
  t :==> b -> t :=> b
  a :--> b -> a :-> b
  l :**  r -> l :*  r


global :: QName -> Type
global n = Right n :$ Nil

bound :: Name T -> Type
bound n = Left n :$ Nil


unForAll :: Has Empty sig m => Type -> m (Name T ::: Type, Type)
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unArrow :: Has Empty sig m => Type -> m (Type, Type)
unArrow = \case{ a :-> b -> pure (a, b) ; _ -> empty }

unProduct :: Has Empty sig m => Type -> m (Type, Type)
unProduct = \case{ l :* r -> pure (l, r) ; _ -> empty }


(.$) :: Type -> Type -> Type
(f :$ as) .$ a = f :$ (as :> a)
(t :=> b) .$ a = subst (singleton (tm t) a) b
_         .$ _ = error "can’t apply non-neutral/forall type"

(.$*) :: Foldable t => Type -> t Type -> Type
f .$* as = foldl' (.$) f as

infixl 9 .$, .$*


instance Substitutable Type where
  subst sub = substitute sub . fvs1


-- FIXME: computation types
-- FIXME: effect signatures
data TypeF t
  = TypeF
  | VoidF
  | UnitF
  | (Name T ::: t) :==> t
  | Either (Name T) QName :$$ Stack t
  | t :--> t
  | t :**  t
  deriving (Foldable, Functor, Show, Traversable)

infixr 0 :==>
infixl 9 :$$
infixr 0 :-->
infixl 7 :**


fold :: (TypeF a -> a) -> Type -> a
fold alg = go
  where
  go = alg . fmap go . out

unfold :: (a -> TypeF a) -> a -> Type
unfold coalg = go
  where
  go = inn . fmap go . coalg


data QType
  = QType
  | QVoid
  | QUnit
  | (UName ::: QType) :===> QType
  | Either QName Index :$$$ Stack (QType)
  | QType :---> QType
  | QType :***  QType
  deriving (Eq, Ord, Show)

infixr 0 :===>
infixl 9 :$$$
infixr 0 :--->
infixl 7 :***
