{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Type.Typed
( Type(..)
, (-->)
, (.+)
, (.*)
, eq
) where

import qualified Data.Kind as K

data Type k t where
  Var :: Int -> Type k t
  Type :: Type K.Type K.Type
  Unit :: Type K.Type ()
  ForAll :: Type K.Type ka -> (Type ka ta -> Type kb tb) -> Type (ka -> kb) (ta -> tb)
  (:$) :: Type (ka -> kb) (ta -> tb) -> Type ka ta -> Type kb tb
  Arr :: Type (K.Type -> K.Type -> K.Type) (ta -> tb -> (ta -> tb))
  Sum :: Type (K.Type -> K.Type -> K.Type) (ta -> tb -> Either ta tb)
  Prd :: Type (K.Type -> K.Type -> K.Type) (ta -> tb -> (ta, tb))

infixl 9 :$

(-->) :: Type K.Type ta -> Type K.Type tb -> Type K.Type (ta -> tb)
a --> b = Arr :$ a :$ b

infixr 0 -->

(.+) :: Type K.Type ta -> Type K.Type tb -> Type K.Type (Either ta tb)
a .+ b = Sum :$ a :$ b

infixl 6 .+

(.*) :: Type K.Type ta -> Type K.Type tb -> Type K.Type (ta, tb)
a .* b = Prd :$ a :$ b

infixl 7 .*


eq :: Type ka ta -> Type kb tb -> Bool
eq = go 0
  where
  go :: Int -> Type ka ta -> Type kb tb -> Bool
  go n = curry $ \case
    (Var n1,       Var n2)       -> n1 == n2
    (Type,         Type)         -> True
    (Unit,         Unit)         -> True
    (ForAll t1 b1, ForAll t2 b2) -> go n t1 t2 && go (n + 1) (b1 (Var n)) (b2 (Var n))
    (f1 :$ a1,     f2 :$ a2)     -> go n f1 f2 && go n a1 a2
    (Arr,          Arr)          -> True
    (Sum,          Sum)          -> True
    (Prd,          Prd)          -> True
    _ -> False
