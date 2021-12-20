module Facet.Functor.Compose
( -- * Composition functor
  type (.)(..)
  -- * Introduction
, liftCInner
, mapCInner
, mapCOuter
, strengthen
, weaken
  -- * Binding syntax
, binder
, Clause(..)
) where

import Control.Applicative (Alternative(..))
import Data.Functor.Identity (Identity(..))

-- Composition functor

newtype (i . j) a = C { runC :: i (j a) }
  deriving (Functor)

instance (Applicative i, Applicative j) => Applicative (i . j) where
  pure = liftCInner . pure
  C f <*> C a = C ((<*>) <$> f <*> a)

instance (Alternative i, Applicative j) => Alternative (i . j) where
  empty = weaken empty
  C l <|> C r = C (l <|> r)


liftCInner :: Applicative i => j a -> (i . j) a
liftCInner = C . pure

mapCInner :: Functor i => (j a -> j' b) -> ((i . j) a -> (i . j') b)
mapCInner f = C . fmap f . runC

mapCOuter :: (i (j a) -> i' (j' b)) -> ((i . j) a -> (i' . j') b)
mapCOuter f = C . f . runC


strengthen :: Applicative m => m (Identity a) -> m a
strengthen = fmap runIdentity

weaken :: (Functor i, Applicative j) => i a -> (i . j) a
weaken = C . fmap pure


-- Binding syntax

binder :: (Functor m, Applicative i) => (forall j . Applicative j => (forall x . i x -> j x) -> j c -> m (j d)) -> m (i (c -> d))
binder c = runC <$> c weaken (liftCInner id)

newtype Clause m i a b = Clause { runClause :: forall j . Applicative j => (forall x . i x -> j x) -> j a -> m (j b) }
