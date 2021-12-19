module Facet.Functor.Compose
( -- * Composition functor
  type (.)(..)
  -- * Introduction
, liftCInner
, mapCInner
, liftCOuter
, mapCOuter
  -- * Binding syntax
, binder
, Clause(..)
) where

import Control.Applicative (Alternative(..))

-- Composition functor

newtype (i . j) a = C { runC :: i (j a) }
  deriving (Functor)

instance (Applicative i, Applicative j) => Applicative (i . j) where
  pure = C . pure . pure
  C f <*> C a = C ((<*>) <$> f <*> a)

instance (Alternative i, Applicative j) => Alternative (i . j) where
  empty = liftCOuter empty
  C l <|> C r = C (l <|> r)


liftCInner :: Applicative i => j a -> (i . j) a
liftCInner = C . pure

mapCInner :: Functor i => (j a -> j' b) -> ((i . j) a -> (i . j') b)
mapCInner f = C . fmap f . runC

liftCOuter :: (Functor i, Applicative j) => i a -> (i . j) a
liftCOuter = C . fmap pure

mapCOuter :: (i (j a) -> i' (j' b)) -> ((i . j) a -> (i' . j') b)
mapCOuter f = C . f . runC


-- Binding syntax

binder :: (Functor m, Applicative i) => (forall j . Applicative j => (forall x . i x -> j x) -> j c -> m (j d)) -> m (i (c -> d))
binder c = runC <$> c liftCOuter (liftCInner id)

newtype Clause m i a b = Clause { runClause :: forall j . Applicative j => (forall x . i x -> j x) -> j a -> m (j b) }
