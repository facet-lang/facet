{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Type.Typed
( Type(..)
, eq
) where

import qualified Data.Kind as K

data Type k r t where
  Var :: Int -> Type r k t
  Type :: Type r K.Type K.Type
  Unit :: Type r K.Type ()
  ForAll :: Type r K.Type ka -> (Type r ka ta -> Type r kb tb) -> Type r (ka -> kb) (ta -> tb)
  (:$) :: Type r (ka -> kb) (ta -> tb) -> Type r ka ta -> Type r kb tb
  (:->) :: Type r K.Type ta -> Type r K.Type tb -> Type r K.Type (ta -> tb)
  (:*) :: Type r K.Type ta -> Type r K.Type tb -> Type r K.Type (ta, tb)

infixl 9 :$
infixr 0 :->
infixl 7 :*

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
    (a1 :-> b1,    a2 :-> b2)    -> go n a1 a2 && go n b1 b2
    (l1 :* r1,     l2 :* r2)     -> go n l1 l2 && go n r1 r2
    _ -> False
