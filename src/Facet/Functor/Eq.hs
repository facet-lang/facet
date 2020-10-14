module Facet.Functor.Eq
( EqM(..)
) where

class EqM f where
  eqM :: (Monad m, Eq a) => f m a -> f m a -> m Bool
