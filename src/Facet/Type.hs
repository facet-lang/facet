{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}
module Facet.Type
( Type(..)
, Type'(..)
, hoistType
, traverseTypeMaybe
, interpretType
) where

import           Data.Foldable (foldl')
import qualified Data.IntMap as IntMap
import           Data.Maybe (fromJust)
import qualified Facet.Core as C
import qualified Facet.Core.HOAS as CH
import           Facet.Deriving
import           Facet.Functor.C
import           Facet.Name
import qualified Facet.Print as P
import           Facet.Syntax

data Type' r
  = Type
  | Unit
  | (Name ::: Type' r) :=> Type' r
  | Either Name r :$ Stack (Type' r)
  | Type' r :-> Type' r
  | Type' r :*  Type' r
  deriving (Foldable, Functor, Traversable)
  deriving (Applicative) via MonadInstance Type'
  deriving (CH.Type) via (CH.Circ (Type' r))

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*

instance Show (Type' P.Print) where
  showsPrec p = showsPrec p . P.prettyWith P.terminalStyle . C.interpret

instance Monad Type' where
  return a = Right a :$ Nil
  t >>= f = rebind f mempty t

instance Scoped (Type' a) where
  maxBV = \case
    Type    -> Nothing
    Unit    -> Nothing
    t :=> _ -> maxBV t
    _ :$ a  -> foldMap maxBV a
    a :-> b -> maxBV a <> maxBV b
    l :* r  -> maxBV l <> maxBV r

instance C.Type (Type' r) where
  tbound n = Left n :$ Nil
  _Type = Type
  _Unit = Unit
  (==>) = (:=>)
  (.$)  = ($$)
  (-->) = (:->)
  (.*)  = (:*)

instance C.Interpret Type' where
  interpret = go
    where
    go = \case
      Type    -> C._Type
      Unit    -> C._Unit
      t :=> b -> fmap go t C.==> go b
      f :$ a  -> foldl' (\ f a -> f C..$ go a) (either C.tbound id f) a
      a :-> b -> go a C.--> go b
      l :* r  -> go l C..*  go r

($$) :: Type' r -> Type' r -> Type' r
(f :$ as) $$ a = f :$ (as :> a)
(t :=> b) $$ a = rebind pure (IntMap.singleton (id' (tm t)) a) b
_         $$ _ = error "can’t apply non-neutral/forall type"

($$*) :: Foldable t => Type' r -> t (Type' r) -> Type' r
f $$* as = foldl' ($$) f as

infixl 9 $$, $$*

rebind :: (r -> Type' r') -> IntMap.IntMap (Type' r') -> Type' r -> Type' r'
rebind g = go
  where
  go e = \case
    Type            -> Type
    Unit            -> Unit
    (n ::: t) :=> b -> (hint n ::: go e t) C.>=> \ v -> go (instantiate n v e) b
    f :$  a         -> either ((e IntMap.!) . id') g f $$* fmap (go e) a
    a :-> b         -> go e a :-> go e b
    l :*  r         -> go e l :* go e r


newtype Type = Abs { inst :: forall r . Type' r }
  deriving (CH.Type) via (CH.Circ Type)

instance Scoped Type where
  maxBV (Abs t) = maxBV t

instance C.Type Type where
  tbound n = Abs $ C.tbound n
  _Type = Abs C._Type
  _Unit = Abs C._Unit

  t ==> b = Abs $ fmap inst t C.==> inst b
  f .$  a = Abs $ inst f C..$  inst a

  a --> b = Abs $ inst a C.--> inst b
  l .*  r = Abs $ inst l C..*  inst r


hoistType :: (forall x . Type' x -> Type' x) -> Type -> Type
hoistType f t = Abs (f (inst t))

traverseTypeMaybe :: (forall x . Type' x -> (Maybe :.: Type') x) -> Type -> Maybe Type
traverseTypeMaybe f t = case f (inst t) of
  C Nothing  -> Nothing
  C (Just _) -> Just (Abs (fromJust (getC (f (inst t)))))


interpretType :: C.Type r => Type -> r
interpretType = C.interpret . inst
