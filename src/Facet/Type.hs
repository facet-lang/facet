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

import           Data.Maybe (fromJust)
import qualified Facet.Core as C
import           Facet.Functor.C
import qualified Facet.Print as P
import           Unsafe.Coerce (unsafeCoerce)

data Type' r
  = Var r
  | Type
  | Unit
  | Type' r :=> (Type' r -> Type' r)
  | Type' r :$  Type' r
  | Type' r :-> Type' r
  | Type' r :*  Type' r

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*

instance Show (Type' P.Print) where
  showsPrec p = showsPrec p . P.prettyWith P.terminalStyle . C.interpret

instance C.Type (Type' r) where
  _Type = Type
  _Unit = Unit
  (>=>) = (:=>)
  (.$)  = (:$)
  (-->) = (:->)
  (.*)  = (:*)

instance C.Interpret Type' where
  interpret = \case
    Var r   -> r
    Type    -> C._Type
    Unit    -> C._Unit
    t :=> b -> C.interpret t C.>=> C.interpret . b . Var
    f :$ a  -> C.interpret f C..$  C.interpret a
    a :-> b -> C.interpret a C.--> C.interpret b
    l :* r  -> C.interpret l C..*  C.interpret r


newtype Type = Abs { inst :: forall r . Type' r }

instance C.Type Type where
  _Type = Abs C._Type
  _Unit = Abs C._Unit

  t >=> b = Abs $ inst t C.>=> inst . b . unsafeCoerce -- I *think* this is justified by the dual parametricity in ForAll1 and again in the quantified constraint. r cannot affect the operation of >=>, so we can safely coerce the argument to its universal quantification
  f .$  a = Abs $ inst f C..$  inst a

  a --> b = Abs $ inst a C.--> inst b
  l .*  r = Abs $ inst l C..*  inst r


hoistType :: (forall x . Type' x -> Type' x) -> Type -> Type
hoistType f t = Abs (f (inst t))

traverseTypeMaybe :: (forall x . Type' x -> (Maybe :.: Type') x) -> Type -> Maybe Type
traverseTypeMaybe f t = case f (inst t) of
  C Nothing  -> Nothing
  C (Just _) -> Just (Abs (fromJust (getC (f (inst t)))))
