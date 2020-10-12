{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Functor.Higher
( type (~>)
, HFunctor(..)
) where

type f ~> g = forall x . f x -> g x

class HFunctor f where
  hmap :: (a ~> b) -> f a ~> f b
