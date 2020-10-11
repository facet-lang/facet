module Facet.Semiring
( Semiring(..)
, Unital(..)
) where

class Semigroup s => Semiring s where
  (><) :: s -> s -> s
  infixr 7 ><

class (Monoid s, Semiring s) => Unital s where
  one :: s
