{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Signature
( None
, absurd
, Sum(..)
, unSum
, Subset(..)
, inj
, prj
, Member
) where

import Control.Applicative ((<|>))
import Control.Lens (Prism', preview, prism', review)
import Data.Functor.Sum
import Data.Kind (Type)

data None a
  deriving (Functor)

absurd :: None a -> b
absurd = \case{}

unSum :: (l a -> b) -> (r a -> b) -> Sum l r a -> b
unSum fl fr = \case
  InL l -> fl l
  InR r -> fr r


class Subset (sub :: Type -> Type) (sup :: Type -> Type) where
  sub :: Prism' (sup a) (sub a)

inj :: Subset sub sup => sub a -> sup a
inj = review sub

prj :: Subset sub sup => sup a -> Maybe (sub a)
prj = preview sub

instance Subset None sig where
  sub = prism' absurd (const Nothing)

instance Subset eff eff where
  sub = prism' id Just

instance Subset eff (Sum eff set) where
  sub = prism' InL (unSum Just (const Nothing))

instance Subset eff (Sum set1 (Sum set2 set3)) => Subset eff (Sum (Sum set1 set2) set3) where
  sub = prism' reassocL reassocR
    where
    reassocL = unSum (InL . InL) (unSum (InL . InR) InR) . inj
    reassocR = prj . unSum (unSum InL (InR . InL)) (InR . InR)

instance (Subset setl sets, Subset setr sets) => Subset (Sum setl setr) sets where
  sub = prism' (unSum inj inj) (\ s -> InL <$> prj s <|> InR <$> prj s)


type Member eff sig = Subset eff sig
