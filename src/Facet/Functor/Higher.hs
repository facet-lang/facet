{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Functor.Higher
( type (~>)
, HFunctor(..)
) where

type f ~> g = forall x . f x -> g x

class (forall a . Functor a => Functor (f a)) => HFunctor f where
  hmap :: (a ~> b) -> f a ~> f b
