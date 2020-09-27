{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Type
( Type(..)
, Type'(..)
, hoistType
, traverseTypeMaybe
) where

import qualified Data.IntMap as IntMap
import           Data.Maybe (fromJust)
import           Data.Text (Text)
import qualified Facet.Core as C
import           Facet.Functor.C
import           Facet.Name
import qualified Facet.Print as P
import           Facet.Syntax
import           Unsafe.Coerce (unsafeCoerce)

data Type' r
  = Var r
  | Bound Name
  | Type
  | Unit
  | (Name ::: Type' r) :=> Type' r
  | Type' r :$  Type' r
  | Type' r :-> Type' r
  | Type' r :*  Type' r

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*

instance Show (Type' P.Print) where
  showsPrec p = showsPrec p . P.prettyWith P.terminalStyle . C.interpret

instance Scoped (Type' a) where
  maxBV = \case
    Var _   -> 0
    Bound _ -> 0
    Type    -> 0
    Unit    -> 0
    t :=> _ -> maxBV t
    f :$ a  -> maxBV f `max` maxBV a
    a :-> b -> maxBV a `max` maxBV b
    l :* r  -> maxBV l `max` maxBV r

instance C.Type (Type' r) where
  _Type = Type
  _Unit = Unit
  (>=>) = (>=>) . (mempty :::)
  (.$)  = (:$)
  (-->) = (:->)
  (.*)  = (:*)

instance C.Interpret Type' where
  interpret = go mempty
    where
    go e = \case
      Var r   -> r
      Bound n -> e IntMap.! id' n
      Type    -> C._Type
      Unit    -> C._Unit
      t :=> b -> go e (ty t) C.>=> \ v -> go (IntMap.insert (id' (tm t)) v e) b
      f :$ a  -> go e f C..$  go e a
      a :-> b -> go e a C.--> go e b
      l :* r  -> go e l C..*  go e r

(>=>) :: (Text ::: Type' r) -> (Type' r -> Type' r) -> Type' r
(n ::: t) >=> b = binder Bound ((:=>) . (::: t)) n b


newtype Type e = Abs { inst :: forall r . Type' r }

instance C.Type (Type e) where
  _Type = Abs C._Type
  _Unit = Abs C._Unit

  t >=> b = Abs $ inst t C.>=> inst . b . unsafeCoerce -- I *think* this is justified by the dual parametricity in ForAll1 and again in the quantified constraint. r cannot affect the operation of >=>, so we can safely coerce the argument to its universal quantification
  f .$  a = Abs $ inst f C..$  inst a

  a --> b = Abs $ inst a C.--> inst b
  l .*  r = Abs $ inst l C..*  inst r


hoistType :: (forall x . Type' x -> Type' x) -> Type e -> Type e
hoistType f t = Abs (f (inst t))

traverseTypeMaybe :: (forall x . Type' x -> (Maybe :.: Type') x) -> Type e -> Maybe (Type e)
traverseTypeMaybe f t = case f (inst t) of
  C Nothing  -> Nothing
  C (Just _) -> Just (Abs (fromJust (getC (f (inst t)))))
