{-# LANGUAGE FunctionalDependencies #-}
module Facet.Quote
( -- * Quotation
  Quote(..)
, quoteBinder
  -- * Deriving
, Quoting(..)
) where

-- Quotation

class Quote v l t | v -> l t where
  quote :: l -> v -> t


quoteBinder :: (Quote v l t, Enum l) => (l -> u) -> l -> (u -> v) -> t
quoteBinder var d f = quote (succ d) (f (var d))


-- Deriving

newtype Quoting l t v = Quoting { getQuoting :: v }

instance (Quote v l t, Num l, Eq t) => Eq (Quoting l t v) where
  Quoting a == Quoting b = quote 0 a == quote 0 b

instance (Quote v l t, Num l, Ord t) => Ord (Quoting l t v) where
  Quoting a `compare` Quoting b = quote 0 a `compare` quote 0 b

instance (Quote v l t, Num l, Show t) => Show (Quoting l t v) where
  showsPrec p = showsPrec p . quote 0 . getQuoting
