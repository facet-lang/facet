module Facet.Semiring
( Semiring(..)
, Unital(..)
, zero
, Few(..)
) where

class Semigroup s => Semiring s where
  (><) :: s -> s -> s
  infixr 7 ><

class (Monoid s, Semiring s) => Unital s where
  one :: s

zero :: Unital s => s
zero = mempty


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
