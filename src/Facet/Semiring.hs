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
