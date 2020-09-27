{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Type
( Type(..)
) where

import qualified Data.Kind as K
import qualified Facet.Core as C
import qualified Facet.Print as P

data Type r k where
  Var :: r k -> Type r k
  Type :: Type r K.Type
  Unit :: Type r K.Type
  (:=>) :: Type r K.Type -> (Type r ka -> Type r kb) -> Type r (ka -> kb)
  (:$) :: Type r (ka -> kb) -> Type r ka -> Type r kb
  (:->) :: Type r K.Type -> Type r K.Type -> Type r K.Type
  (:*) :: Type r K.Type -> Type r K.Type -> Type r K.Type

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*

instance Show (Type (P.TPrint sig) k) where
  showsPrec p = showsPrec p . P.prettyWith P.terminalStyle . P.runTPrint . C.interpret

instance C.Type (Type r) where
  _Type = Type
  _Unit = Unit
  (>=>) = (:=>)
  (.$)  = (:$)
  (-->) = (:->)
  (.*)  = (:*)

instance C.Interpret Type where
  interpret = \case
    Var r   -> r
    Type    -> C._Type
    Unit    -> C._Unit
    t :=> b -> C.interpret t C.>=> C.interpret . b . Var
    f :$ a  -> C.interpret f C..$  C.interpret a
    a :-> b -> C.interpret a C.--> C.interpret b
    l :* r  -> C.interpret l C..*  C.interpret r
