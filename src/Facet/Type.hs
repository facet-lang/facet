{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Type
( Type(..)
) where

import qualified Facet.Core as C
import qualified Facet.Core.Lifted as CL
import           Facet.Functor.C
import           Facet.Functor.I

data Type env ty
  = Var (env ty)
  | Type
  | Unit
  | Type env ty :* Type env ty
  | Type env ty :$ Type env ty
  | Type env ty :-> Type env ty
  | ForAll (Type env ty) (forall env' . Extends env env' => Type env' ty -> Type env' ty)

infixl 7 :*
infixr 0 :->
infixl 9 :$

instance (Eq ty, Num ty) => Eq (Type I ty) where
  (==) = go 0
    where
    go n = curry $ \case
      (Var a1, Var a2) -> a1 == a2
      (Type, Type) -> True
      (Unit, Unit) -> True
      (l1 :* r1, l2 :* r2) -> go n l1 l2 && go n r1 r2
      (f1 :$ a1, f2 :$ a2) -> go n f1 f2 && go n a1 a2
      (a1 :-> b1, a2 :-> b2) -> go n a1 a2 && go n b1 b2
      (ForAll t1 b1, ForAll t2 b2) -> go n t1 t2 && go (n + 1) (b1 (Var n)) (b2 (Var n))
      _ -> False

instance C.Type (Type env ty) where
  _Type = Type
  _Unit = Unit
  (.*) = (:*)
  (-->) = (:->)
  (>=>) = undefined -- FIXME: we can’t implement this any more because ForAll requires and returns in an extended environment.
  (.$) = (:$)

instance C.Interpret (Type I) where
  interpret = getI . getI . CL.interpretA

instance CL.InterpretA Type where
  interpretA = \case
    Var v -> pure v
    Type -> CL._Type
    Unit -> CL._Unit
    f :$ a -> CL.interpretA f CL..$ CL.interpretA a
    l :* r -> CL.interpretA l CL..* CL.interpretA r
    a :-> b -> CL.interpretA a CL.--> CL.interpretA b
    ForAll t b -> CL.interpretA t CL.>=> CL.interpretA . b . Var
