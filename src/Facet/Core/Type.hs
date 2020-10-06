{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
module Facet.Core.Type
( Type(..)
, interpret
, rename
, subst
, TypeF(..)
) where

import           Control.Category ((>>>))
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
  _Type = In $ Type
  _Void = In $ Void
  _Unit = In $ Unit
  (>=>) = fmap In . (:=>)
  (.$)  = ($$)
  (-->) = fmap In . (:->)
  (.*)  = fmap In . (:*)

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
