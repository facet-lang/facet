{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Type
( Type(..)
, Type'(..)
, hoistType
, CompL(..)
, traverseTypeMaybe
) where

import qualified Data.Kind as K
import           Data.Maybe (fromJust)
import qualified Facet.Core as C
import qualified Facet.Print as P
import           Unsafe.Coerce (unsafeCoerce)

data Type' r k where
  Var :: r k -> Type' r k
  Type :: Type' r K.Type
  Unit :: Type' r K.Type
  (:=>) :: Type' r K.Type -> (Type' r ka -> Type' r kb) -> Type' r (ka -> kb)
  (:$) :: Type' r (ka -> kb) -> Type' r ka -> Type' r kb
  (:->) :: Type' r K.Type -> Type' r K.Type -> Type' r K.Type
  (:*) :: Type' r K.Type -> Type' r K.Type -> Type' r K.Type

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*

instance Show (Type' (P.TPrint sig) k) where
  showsPrec p = showsPrec p . P.prettyWith P.terminalStyle . P.runTPrint . C.interpret

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


newtype Type k = Abs { inst :: forall r . Type' r k }

instance C.Type Type where
  _Type = Abs C._Type
  _Unit = Abs C._Unit

  t >=> b = Abs $ inst t C.>=> inst . b . unsafeCoerce -- I *think* this is justified by the dual parametricity in ForAll1 and again in the quantified constraint. r cannot affect the operation of >=>, so we can safely coerce the argument to its universal quantification
  f .$  a = Abs $ inst f C..$  inst a

  a --> b = Abs $ inst a C.--> inst b
  l .*  r = Abs $ inst l C..*  inst r


hoistType :: (forall x . Type' x a -> Type' x a) -> Type a -> Type a
hoistType f t = Abs (f (inst t))

newtype CompL f g r a = CompL { getCompL :: f (g r a) }

traverseTypeMaybe :: (forall x . Type' x a -> CompL Maybe Type' x a) -> Type a -> Maybe (Type a)
traverseTypeMaybe f t = case f (inst t) of
  CompL Nothing  -> Nothing
  CompL (Just _) -> Just (Abs (fromJust (getCompL (f (inst t)))))
