{-# LANGUAGE FunctionalDependencies #-}
module Facet.Semiring
( Semiring(..)
, Unital(..)
, zero
, LeftModule(..)
, scalarMultDefault
, Few(..)
) where

class Semigroup s => Semiring s where
  (><) :: s -> s -> s
  infixr 7 ><

class (Monoid s, Semiring s) => Unital s where
  one :: s

zero :: Unital s => s
zero = mempty


class (Semiring r, Semigroup m) => LeftModule r m | m -> r where
  (><<) :: r -> m -> m
  infixr 7 ><<

scalarMultDefault :: (Semiring r, Functor f) => r -> f r -> f r
scalarMultDefault = fmap . (><)

instance Semiring r => LeftModule r [r] where
  r ><< rs = map (r ><) rs


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
