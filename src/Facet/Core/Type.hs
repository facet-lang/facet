{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
module Facet.Core.Type
( Type(..)
, forAll_
, arrow_
, app_
, prd_
, interpret
, rename
, subst
, TypeF(..)
, fold
) where

import           Control.Category ((>>>))
import           Control.Lens.Prism hiding (_Void)
import           Data.Foldable (foldl')
import qualified Facet.Core as C
import           Facet.Name
import           Facet.Stack
import           Facet.Syntax
import           Facet.Vars

newtype Type = In { out :: TypeF Type }
  deriving (C.Type)

instance Scoped Type where
  fvs = out >>> \case
    Type    -> mempty
    Void    -> mempty
    Unit    -> mempty
    t :=> b -> fvs (ty t) <> bind (tm t) (fvs b)
    f :$ a  -> either singleton (const mempty) f <> foldMap fvs a
    a :-> b -> fvs a <> fvs b
    l :* r  -> fvs l <> fvs r


forAll_ :: Prism' Type (Name T ::: Type, Type)
forAll_ = prism' (In . uncurry (:=>)) (\case{ In (t :=> b) -> Just (t, b) ; _ -> Nothing })

arrow_ :: Prism' Type (Type, Type)
arrow_ = prism' (In . uncurry (:->)) (\case{ In (a :-> b) -> Just (a, b) ; _ -> Nothing })

app_ :: Prism' Type (Type, Type)
app_ = prism' (uncurry ($$)) (\case{ In (f :$ (as :> a)) -> Just (In (f :$ as), a) ; _ -> Nothing })

prd_ :: Prism' Type (Type, Type)
prd_ = prism' (In . uncurry (:*)) (\case{ In (l :* r) -> Just (l, r) ; _ -> Nothing })


interpret :: C.Type r => Type -> r
interpret = go
  where
  go = out >>> \case
    Type    -> C._Type
    Void    -> C._Void
    Unit    -> C._Unit
    t :=> b -> fmap go t C.>=> go b
    f :$ a  -> foldl' (\ f a -> f C..$ go a) (either C.tbound C.tglobal f) a
    a :-> b -> go a C.--> go b
    l :* r  -> go l C..*  go r


($$) :: Type -> Type -> Type
In (f :$ as) $$ a = In $ f :$ (as :> a)
In (t :=> b) $$ a = subst (tm t) a b
_            $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: Foldable t => Type -> t Type -> Type
f $$* as = foldl' ($$) f as

infixl 9 $$, $$*

rename :: Name T -> Name T -> Type -> Type
rename x y = go
  where
  go = out >>> \case
    Type          -> C._Type
    Void          -> C._Void
    Unit          -> C._Unit
    (z ::: t) :=> b
      | x == z    -> (z ::: go t) C.>=>    b
      | otherwise -> (z ::: go t) C.>=> go b
    f :$ as       -> either (\ z -> C.tbound (if z == x then y else z)) C.tglobal f $$* fmap go as
    a :-> b       -> go a C.--> go b
    l :*  r       -> go l C..*  go r

subst :: Name T -> Type -> Type -> Type
subst x e = go
  where
  go =  out >>> \case
    Type            -> C._Type
    Void            -> C._Void
    Unit            -> C._Unit
    (n ::: t) :=> b ->
      let n' = prime (hint n) (fvs b <> fvs e)
          b' = go (rename n n' b)
      in (n' ::: go t) C.>=> b'
    f :$  as
      | Left f <- f
      , f == x      -> e $$* fmap go as
      | otherwise   -> either C.tbound C.tglobal f $$* fmap go as
    a :-> b         -> go a C.--> go b
    l :*  r         -> go l C..*  go r


-- FIXME: computation types
-- FIXME: effect signatures
data TypeF t
  = Type
  | Void
  | Unit
  | (Name T ::: t) :=> t
  | Either (Name T) QName :$ Stack t
  | t :-> t
  | t :*  t
  deriving (Foldable, Functor, Show, Traversable)

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*

instance C.Type (TypeF Type) where
  tglobal n = Right n :$ Nil
  tbound n = Left n :$ Nil
  _Type = Type
  _Void = Void
  _Unit = Unit
  t >=> b = fmap In t :=> In b
  f .$  a = out $ In f $$ In a
  a --> b = In a :-> In b
  l .*  r = In l :* In r


fold :: (TypeF a -> a) -> Type -> a
fold alg = go
  where
  go = alg . fmap go . out
