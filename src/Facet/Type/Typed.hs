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

data Type k r t where
  Var :: Int -> Type r k t
  Type :: Type r K.Type K.Type
  Unit :: Type r K.Type ()
  ForAll :: Type r K.Type ka -> (Type r ka ta -> Type r kb tb) -> Type r (ka -> kb) (ta -> tb)
  (:$) :: Type r (ka -> kb) (ta -> tb) -> Type r ka ta -> Type r kb tb
  Arr :: Type r (K.Type -> K.Type -> K.Type) (ta -> tb -> (ta -> tb))
  Sum :: Type r (K.Type -> K.Type -> K.Type) (ta -> tb -> Either ta tb)
  Prd :: Type r (K.Type -> K.Type -> K.Type) (ta -> tb -> (ta, tb))

infixl 9 :$

(-->) :: Type r K.Type ta -> Type r K.Type tb -> Type r K.Type (ta -> tb)
a --> b = Arr :$ a :$ b

infixr 0 -->

(.+) :: Type r K.Type ta -> Type r K.Type tb -> Type r K.Type (Either ta tb)
a .+ b = Sum :$ a :$ b

infixl 6 .+

(.*) :: Type r K.Type ta -> Type r K.Type tb -> Type r K.Type (ta, tb)
a .* b = Prd :$ a :$ b

infixl 7 .*


eq :: Type r ka ta -> Type r kb tb -> Bool
eq = go 0
  where
  go :: Int -> Type r ka ta -> Type r kb tb -> Bool
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
