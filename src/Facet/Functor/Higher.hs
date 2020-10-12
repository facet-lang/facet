{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Functor.Higher
( type (~>)
) where

type f ~> g = forall x . f x -> g x
