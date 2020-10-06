{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
, rename
, subst
, TypeF(..)
, fold
, Interpret(..)
) where

import           Control.Category ((>>>))
import           Control.Lens.Prism hiding (_Void)
import           Data.Foldable (foldl')
import qualified Data.IntSet as IntSet
import qualified Facet.Core as C
import           Facet.Name
import           Facet.Syntax

newtype Type = In { out :: TypeF Type }

instance Scoped Type where
  fvs = out >>> \case
    Type    -> mempty
    Void    -> mempty
    Unit    -> mempty
    t :=> b -> IntSet.delete (id' (tm t)) (fvs b)
    f :$ a  -> either (IntSet.insert . id') (const id) f (foldMap fvs a)
    a :-> b -> fvs a <> fvs b
    l :* r  -> fvs l <> fvs r

instance C.Type Type where
  tglobal n = In $ Right n :$ Nil
  tbound n = In $ Left n :$ Nil
  _Type = In Type
  _Void = In Void
  _Unit = In Unit
  (>=>) = fmap In . (:=>)
  (.$)  = ($$)
  (-->) = fmap In . (:->)
  (.*)  = fmap In . (:*)

forAll_ :: Prism' Type (Name ::: Type, Type)
forAll_ = prism' (In . uncurry (:=>)) (\case{ In (t :=> b) -> Just (t, b) ; _ -> Nothing })

arrow_ :: Prism' Type (Type, Type)
arrow_ = prism' (In . uncurry (:->)) (\case{ In (a :-> b) -> Just (a, b) ; _ -> Nothing })

app_ :: Prism' Type (Type, Type)
app_ = prism' (uncurry ($$)) (\case{ In (f :$ (as :> a)) -> Just (In (f :$ as), a) ; _ -> Nothing })

prd_ :: Prism' Type (Type, Type)
prd_ = prism' (In . uncurry (:*)) (\case{ In (l :* r) -> Just (l, r) ; _ -> Nothing })

($$) :: Type -> Type -> Type
In (f :$ as) $$ a = In $ f :$ (as :> a)
In (t :=> b) $$ a = subst (tm t) a b
_            $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: Foldable t => Type -> t Type -> Type
f $$* as = foldl' ($$) f as

infixl 9 $$, $$*

rename :: Name -> Name -> Type -> Type
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

subst :: Name -> Type -> Type -> Type
subst x e = go
  where
  go =  out >>> \case
    Type            -> C._Type
    Void            -> C._Void
    Unit            -> C._Unit
    (n ::: t) :=> b -> let n' = prime (hint n) (fvs b <> fvs e)
                           b' = go (rename n n' b)
                       in (n' ::: go t) C.>=> b'
    f :$  as
      | Left f <- f
      , f == x      -> e $$* fmap go as
      | otherwise   -> either C.tbound C.tglobal f $$* fmap go as
    a :-> b         -> go a C.--> go b
    l :*  r         -> go l C..*  go r


data TypeF t
  = Type
  | Void
  | Unit
  | (Name ::: t) :=> t
  | Either Name QName :$ Stack t
  | t :-> t
  | t :*  t
  deriving (Foldable, Functor, Show, Traversable)

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*


fold :: (TypeF a -> a) -> Type -> a
fold alg = go
  where
  go = alg . fmap go . out


class Interpret i r where
  interpret :: i -> r

instance C.Type r => Interpret Type r where
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

instance C.Type r => Interpret (TypeF Type) r where
  interpret = interpret . In
