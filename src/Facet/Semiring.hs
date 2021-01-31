{-# LANGUAGE FunctionalDependencies #-}
module Facet.Semiring
( -- * Semiring classes
  Semiring(..)
, Unital(..)
, zero
  -- * Module classes
, LeftModule(..)
, scaleDefault
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

scaleDefault :: (Semiring r, Functor f) => r -> f r -> f r
scaleDefault = fmap . (><)

instance Semiring r => LeftModule r [r] where
  (><<) = scaleDefault

instance Semiring r => LeftModule r (Maybe r) where
  (><<) = scaleDefault


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
