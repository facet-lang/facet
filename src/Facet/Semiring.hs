module Facet.Semiring
( Semiring(..)
) where

class Semigroup s => Semiring s where
  (><) :: s -> s -> s
  infixr 7 ><
