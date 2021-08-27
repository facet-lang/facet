module Facet.Functor.Compose
( -- * Composition functor
  type (.)(..)
  -- * Introduction
, liftCInner
, mapCInner
, liftCOuter
, mapCOuter
) where

import Facet.Syntax (type (~>))

-- Composition functor

newtype (i . j) a = C { runC :: i (j a) }
  deriving (Functor)

instance (Applicative i, Applicative j) => Applicative (i . j) where
  pure = C . pure . pure
  C f <*> C a = C ((<*>) <$> f <*> a)


liftCInner :: Applicative i => j a -> (i . j) a
liftCInner = C . pure

mapCInner :: Functor i => (j ~> j') -> ((i . j) ~> (i . j'))
mapCInner f = C . fmap f . runC

liftCOuter :: (Functor i, Applicative j) => i a -> (i . j) a
liftCOuter = C . fmap pure

mapCOuter :: (i ~> i') -> ((i . j) ~> (i' . j))
mapCOuter f = C . f . runC
