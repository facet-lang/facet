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
, global_
, bound_
, type_
, unit_
, void_
, forAll_
, arrow_
, app_
, app'_
, prd_
, TypeF(..)
, fold
, unfold
) where

import Control.Lens (Prism', prism', review, _Left, _Right)
import Data.Foldable (foldl')
import Facet.Name
import Facet.Stack
import Facet.Substitution as Subst
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

instance Scoped Type where
  fvs = fvsDefault

instance Scoped1 Type where
  fvs1 = \case
    Type    -> pure (review type_ ())
    Void    -> pure (review void_ ())
    Unit    -> pure (review unit_ ())
    t :=> b -> mk <$> fvs1 (ty t) <*> bind1 (review bound_) (tm t) (fvs b) (fvs1 b)
      where
      mk t' (n', b') = review forAll_ (n' ::: t', b')
    f :$ as -> f' <*> traverse fvs1 as
      where
      f' = case f of
        Left f -> ($$*) <$> boundVar1 (review bound_) f
        _      -> pure (curry (review app'_) f)
    a :-> b -> curry (review arrow_) <$> fvs1 a <*> fvs1 b
    l :* r  -> curry (review prd_) <$> fvs1 l <*> fvs1 r


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


var_ :: Prism' Type (Either (Name T) QName)
var_ = prism' (:$ Nil) (\case { f :$ Nil -> Just f ; _ -> Nothing })

global_ :: Prism' Type QName
global_ = var_ . _Right

bound_ :: Prism' Type (Name T)
bound_ = var_ . _Left


type_ :: Prism' Type ()
type_ = prism' (const Type) (\case{ Type -> Just () ; _ -> Nothing })

unit_ :: Prism' Type ()
unit_ = prism' (const Unit) (\case{ Unit -> Just () ; _ -> Nothing })

void_ :: Prism' Type ()
void_ = prism' (const Void) (\case{ Void -> Just () ; _ -> Nothing })


forAll_ :: Prism' Type (Name T ::: Type, Type)
forAll_ = prism' (uncurry (:=>)) (\case{ t :=> b -> Just (t, b) ; _ -> Nothing })

arrow_ :: Prism' Type (Type, Type)
arrow_ = prism' (uncurry (:->)) (\case{ a :-> b -> Just (a, b) ; _ -> Nothing })

app_ :: Prism' Type (Type, Type)
app_ = prism' (uncurry ($$)) (\case{ f :$ (as :> a) -> Just (f :$ as, a) ; _ -> Nothing })

app'_ :: Prism' Type (Either (Name T) QName, Stack Type)
app'_ = prism' (uncurry (:$)) (\case{ f :$ as -> Just (f, as) ; _ -> Nothing })

prd_ :: Prism' Type (Type, Type)
prd_ = prism' (uncurry (:*)) (\case{ l :* r -> Just (l, r) ; _ -> Nothing })


($$) :: Type -> Type -> Type
(f :$ as) $$ a = f :$ (as :> a)
(t :=> b) $$ a = subst (singleton (tm t) a) b
_         $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: Foldable t => Type -> t Type -> Type
f $$* as = foldl' ($$) f as

infixl 9 $$, $$*


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

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*


fold :: (TypeF a -> a) -> Type -> a
fold alg = go
  where
  go = alg . fmap go . out

unfold :: (a -> TypeF a) -> a -> Type
unfold coalg = go
  where
  go = inn . fmap go . coalg
