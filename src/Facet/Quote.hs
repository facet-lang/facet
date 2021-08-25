{-# LANGUAGE FunctionalDependencies #-}
module Facet.Quote
( -- * Quotation
  Quote(..)
, quoteBinder
, Quote1(..)
  -- * Deriving
, Quoting(..)
) where

import Facet.Name (Level)

-- Quotation

class Quote v t | v -> t where
  quote :: Level -> v -> t


quoteBinder :: Quote v t => (Level -> u) -> Level -> (u -> v) -> t
quoteBinder var d f = quote (succ d) (f (var d))


class Quote1 v t | v -> t where
  liftQuoteWith :: (Level -> u -> s) -> Level -> v u -> t s


-- Deriving

newtype Quoting t v = Quoting { getQuoting :: v }

instance (Quote v t, Eq t) => Eq (Quoting t v) where
  Quoting a == Quoting b = quote 0 a == quote 0 b

instance (Quote v t, Ord t) => Ord (Quoting t v) where
  Quoting a `compare` Quoting b = quote 0 a `compare` quote 0 b

instance (Quote v t, Show t) => Show (Quoting t v) where
  showsPrec p = showsPrec p . quote 0 . getQuoting
