{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Type.Typed
( Type(..)
, SomeType(..)
) where

import qualified Data.Kind as K
import qualified Facet.Core.Typed as CT
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
  showsPrec p = showsPrec p . P.prettyWith P.terminalStyle . P.runTPrint . CT.interpret

instance CT.Interpret Type where
  interpret = \case
    Var r   -> r
    Type    -> CT._Type
    Unit    -> CT._Unit
    t :=> b -> CT.interpret t CT.>=> CT.interpret . b . Var
    f :$ a  -> CT.interpret f CT..$  CT.interpret a
    a :-> b -> CT.interpret a CT.--> CT.interpret b
    l :* r  -> CT.interpret l CT..*  CT.interpret r


data SomeType r where
  SomeType :: Type r k -> SomeType r
