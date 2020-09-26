{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Type.Typed
( Type(..)
, interpret
, SomeType(..)
) where

import qualified Data.Kind as K
import qualified Facet.Core as C
import qualified Facet.Print as P

data Type k r where
  Var :: r -> Type k r
  Type :: Type K.Type r
  Unit :: Type K.Type r
  (:=>) :: Type K.Type r -> (Type ka r -> Type kb r) -> Type (ka -> kb) r
  (:$) :: Type (ka -> kb) r -> Type ka r -> Type kb r
  (:->) :: Type K.Type r -> Type K.Type r -> Type K.Type r
  (:*) :: Type K.Type r -> Type K.Type r -> Type K.Type r

infixr 0 :=>
infixl 9 :$
infixr 0 :->
infixl 7 :*

instance Show (Type k P.Print) where
  showsPrec p = showsPrec p . P.prettyWith P.terminalStyle . interpret

interpret :: C.Type r => Type k r -> r
interpret = \case
  Var r   -> r
  Type    -> C._Type
  Unit    -> C._Unit
  t :=> b -> interpret t C.>=> interpret . b . Var
  f :$ a  -> interpret f C..$  interpret a
  a :-> b -> interpret a C.--> interpret b
  l :* r  -> interpret l C..*  interpret r


data SomeType r where
  SomeType :: Type r k -> SomeType r
