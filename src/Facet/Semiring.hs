{-# LANGUAGE FunctionalDependencies #-}
module Facet.Semiring
( -- * Semiring classes
  Semiring(..)
, Unital(..)
, zero
  -- * Module classes
, LeftModule(..)
, scalarMultDefault
  -- * Semiring datatypes
, Few(..)
) where

-- Semiring classes

class Semigroup s => Semiring s where
  (><) :: s -> s -> s
  infixr 7 ><

class (Monoid s, Semiring s) => Unital s where
  one :: s

zero :: Unital s => s
zero = mempty


-- Module classes

class (Semiring r, Semigroup m) => LeftModule r m | m -> r where
  (><<) :: r -> m -> m
  infixr 7 ><<

scalarMultDefault :: (Semiring r, Functor f) => r -> f r -> f r
scalarMultDefault = fmap . (><)

instance Semiring r => LeftModule r [r] where
  (><<) = scalarMultDefault

instance Semiring r => LeftModule r (Maybe r) where
  (><<) = scalarMultDefault


-- Semiring datatypes

data Few
  = Zero
  | One
  | Many
  deriving (Bounded, Enum, Eq, Ord, Show)

instance Semigroup Few where
  Zero <> b    = b
  a    <> Zero = a
  _    <> _    = Many

instance Monoid Few where
  mempty = Zero

instance Semiring Few where
  Zero >< _    = Zero
  _    >< Zero = Zero
  a    >< b    = max a b

instance Unital Few where
  one = One
