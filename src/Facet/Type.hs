{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
module Facet.Type
( Type(..)
, subst
) where

import           Control.Applicative (liftA2)
import           Data.Foldable (foldl')
import qualified Data.IntMap as IntMap
import           Data.Text (Text)
import qualified Facet.Core as C
import qualified Facet.Core.HOAS as CH
import           Facet.Name
import qualified Facet.Print as P
import           Facet.Syntax

data Type
  = Type
  | Unit
  | (Name ::: Type) :=> Type
  | Either Name Text :$  Stack Type
  | Type :-> Type
  | Type :*  Type

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*

instance Show Type where
  showsPrec p = showsPrec p . P.getPrint . C.interpret

instance Scoped Type where
  maxBV = \case
    Type    -> Nothing
    Unit    -> Nothing
    t :=> _ -> maxBV t
    _ :$ a  -> foldMap maxBV a
    a :-> b -> maxBV a <> maxBV b
    l :* r  -> maxBV l <> maxBV r

instance CH.Type Type where
  tglobal = pure . C.tglobal

  _Type = pure C._Type
  _Unit = pure C._Unit

  t >=> b = t >>= \ (n ::: t) -> binderM C.tbound ((C.==>) . (::: t)) n b
  f .$  a = liftA2 (C..$)  f a

  a --> b = liftA2 (C.-->) a b
  l .*  r = liftA2 (C..*)  l r

instance C.Type Type where
  tglobal n = Right n :$ Nil
  tbound n = Left n :$ Nil
  _Type = Type
  _Unit = Unit
  (==>) = (:=>)
  (.$)  = ($$)
  (-->) = (:->)
  (.*)  = (:*)

instance C.Interpret Type where
  interpret = go
    where
    go = \case
      Type    -> C._Type
      Unit    -> C._Unit
      t :=> b -> fmap go t C.==> go b
      f :$ a  -> foldl' (\ f a -> f C..$ go a) (either C.tbound C.tglobal f) a
      a :-> b -> go a C.--> go b
      l :* r  -> go l C..*  go r

($$) :: Type -> Type -> Type
(f :$ as) $$ a = f :$ (as :> a)
(t :=> b) $$ a = subst (IntMap.singleton (id' (tm t)) a) b
_         $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: Foldable t => Type -> t Type -> Type
f $$* as = foldl' ($$) f as

infixl 9 $$, $$*

subst :: IntMap.IntMap Type -> Type -> Type
subst e = \case
  Type            -> Type
  Unit            -> Unit
  (n ::: t) :=> b -> (hint n ::: subst e t) C.>=> \ v -> subst (instantiate n v e) b
  f :$  a
    | Left f <- f -> (e IntMap.! id' f) $$* fmap (subst e) a
    | otherwise   -> f :$ fmap (subst e) a
  a :-> b         -> subst e a :-> subst e b
  l :*  r         -> subst e l :* subst e r
