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
, Tropical(..)
) where

-- Semiring classes

-- | Semirings extend 'Semigroup's with an '><' (multiplication) operation satisfying:
--
-- Associativity:
--
-- @
-- a >< (b >< c) ≡ (a >< b) >< c
-- @
--
-- Left-distributivity:
--
-- @
-- a >< (b <> c) ≡ (a >< b) <> (a >< c)
-- @
--
-- Right-distributivity:
--
-- @
-- (a <> b) >< c ≡ (a >< c) <> (b >< c)
-- @
--
-- Contrary to many presentations, we do not require '<>' (addition) to be commutative, or for the type to be a 'Monoid'. However, if it /is/ a 'Monoid', then we additionally require '><' to satisfy:
--
-- Left-annihilation:
--
-- @
-- zero >< a ≡ zero
-- @
--
-- Right-annihilation:
--
-- @
-- a >< zero ≡ zero
-- @
--
-- where 'zero' is a synonym for 'mempty', defined below.
class Semigroup s => Semiring s where
  (><) :: s -> s -> s
  infixr 7 ><

instance Semiring () where
  _ >< _ = ()

instance (Semiring a, Semiring b) => Semiring (a, b) where
  (a1, b1) >< (a2, b2) = (a1 >< a2, b1 >< b2)

instance (Semiring a, Semiring b, Semiring c) => Semiring (a, b, c) where
  (a1, b1, c1) >< (a2, b2, c2) = (a1 >< a2, b1 >< b2, c1 >< c2)


-- | Unital semirings extend 'Semiring's with a multiplicative unit, 'one', satisfyiing:
--
-- Left-identity:
--
-- @
-- one >< a ≡ a
-- @
--
-- Right-identity:
--
-- @
-- a >< one ≡ a
-- @
class (Monoid s, Semiring s) => Unital s where
  one :: s

instance Unital () where
  one = ()

instance (Unital a, Unital b) => Unital (a, b) where
  one = (one, one)

instance (Unital a, Unital b, Unital c) => Unital (a, b, c) where
  one = (one, one, one)


zero :: Unital s => s
zero = mempty


-- Module classes

-- | A left /R/-module /M/ (for a 'Semiring' /R/) is a 'Semigroup' extended with a '><<' (scalar multiplication) operation satisfying:
--
-- Left-distributivity of ><< over <> (on /M/):
--
-- @
-- r ><< (m <> n) ≡ r ><< m <> r ><< n
-- @
--
-- Left-distributivity of <> (on /R/) over ><<:
--
-- @
-- (r <> s) ><< m ≡ r ><< m <> s ><< m
-- @
--
-- Associativity:
--
-- @
-- (r >< s) ><< m ≡ r ><< (s ><< m)
-- @
class (Semiring r, Semigroup m) => LeftModule r m | m -> r where
  (><<) :: r -> m -> m
  infixr 7 ><<

scaleDefault :: (Semiring r, Functor f) => r -> f r -> f r
scaleDefault = fmap . (><)

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


data Tropical a
  = Finite a
  | Infinity
  deriving (Eq, Ord, Show)

instance Ord a => Semigroup (Tropical a) where
  (<>) = min

instance Ord a => Monoid (Tropical a) where
  mempty = Infinity

instance (Num a, Ord a) => Semiring (Tropical a) where
  Infinity >< _        = Infinity
  _        >< Infinity = Infinity
  Finite a >< Finite b = Finite (a + b)

instance (Num a, Ord a) => Unital (Tropical a) where
  one = Finite 0
