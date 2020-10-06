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
) where

import           Data.Bifunctor (first)
import           Data.Foldable (foldl')
import qualified Data.IntSet as IntSet
import qualified Facet.Core as C
import           Facet.Name
import           Facet.Syntax

data Type
  = Type
  | Void
  | Unit
  | (Name ::: Type) :=> Type
  | Either Name QName :$ Stack Type
  | Type :-> Type
  | Type :*  Type
  deriving (Show)

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*

instance Scoped Type where
  fvs = \case
    Type    -> mempty
    Void    -> mempty
    Unit    -> mempty
    t :=> b -> IntSet.delete (id' (tm t)) (fvs b)
    f :$ a  -> either (IntSet.insert . id') (const id) f (foldMap fvs a)
    a :-> b -> fvs a <> fvs b
    l :* r  -> fvs l <> fvs r

instance C.Type Type where
  tglobal n = Right n :$ Nil
  tbound n = Left n :$ Nil
  _Type = Type
  _Void = Void
  _Unit = Unit
  (>=>) = (:=>)
  (.$)  = ($$)
  (-->) = (:->)
  (.*)  = (:*)

interpret :: C.Type r => Type -> r
interpret = go
    where
    go = \case
      Type    -> C._Type
      Void    -> C._Void
      Unit    -> C._Unit
      t :=> b -> fmap go t C.>=> go b
      f :$ a  -> foldl' (\ f a -> f C..$ go a) (either C.tbound C.tglobal f) a
      a :-> b -> go a C.--> go b
      l :* r  -> go l C..*  go r

($$) :: Type -> Type -> Type
(f :$ as) $$ a = f :$ (as :> a)
(t :=> b) $$ a = subst (tm t) a b
_         $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: Foldable t => Type -> t Type -> Type
f $$* as = foldl' ($$) f as

infixl 9 $$, $$*

rename :: Name -> Name -> Type -> Type
rename x y = go
  where
  go = \case
    Type          -> Type
    Void          -> Void
    Unit          -> Unit
    (z ::: t) :=> b
      | x == z    -> (z ::: go t) :=>    b
      | otherwise -> (z ::: go t) :=> go b
    f :$ as       -> first (\ z -> if z == x then y else z) f :$ fmap go as
    a :-> b       -> go a :-> go b
    l :*  r       -> go l :*  go r

subst :: Name -> Type -> Type -> Type
subst x e = go
  where
  go =  \case
    Type            -> Type
    Void            -> Void
    Unit            -> Unit
    (n ::: t) :=> b -> let n' = prime (hint n) (fvs b <> fvs e)
                           b' = go (rename n n' b)
                       in (n' ::: go t) C.>=> b'
    f :$  a
      | Left f <- f
      , f == x      -> e $$* (go <$> a)
      | otherwise   -> f :$  (go <$> a)
    a :-> b         -> go a :-> go b
    l :*  r         -> go l :*  go r
