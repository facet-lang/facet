module Facet.Functor.Compose
( -- * Composition functor
  type (.)(..)
  -- * Introduction
, liftCInner
) where

-- Composition functor

newtype (i . j) a = C { runC :: i (j a) }
  deriving (Functor)

instance (Applicative i, Applicative j) => Applicative (i . j) where
  pure = C . pure . pure
  C f <*> C a = C ((<*>) <$> f <*> a)


liftCInner :: Applicative i => j a -> (i . j) a
liftCInner = C . pure
