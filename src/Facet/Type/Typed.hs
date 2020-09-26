{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Type.Typed
( Type(..)
, eq
, interpret
, SomeType(..)
) where

import qualified Data.Kind as K
import qualified Facet.Core as C

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

eq :: Type ka Int -> Type kb Int -> Bool
eq = go 0
  where
  go :: Int -> Type ka Int -> Type kb Int -> Bool
  go n = curry $ \case
    (Var n1,    Var n2)    -> n1 == n2
    (Type,      Type)      -> True
    (Unit,      Unit)      -> True
    (t1 :=> b1, t2 :=> b2) -> go n t1 t2 && go (n + 1) (b1 (Var n)) (b2 (Var n))
    (f1 :$ a1,  f2 :$ a2)  -> go n f1 f2 && go n a1 a2
    (a1 :-> b1, a2 :-> b2) -> go n a1 a2 && go n b1 b2
    (l1 :* r1,  l2 :* r2)  -> go n l1 l2 && go n r1 r2
    _ -> False

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
