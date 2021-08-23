{-# LANGUAGE FunctionalDependencies #-}
module Facet.Quote
( -- * Quotation
  Quote(..)
, quoteBinder
  -- * Deriving
, Quoting(..)
) where

import Facet.Name (Level)

-- Quotation

class Quote v t | v -> t where
  quote :: Level -> v -> t


quoteBinder :: Quote v t => (Level -> v) -> Level -> (v -> v) -> t
quoteBinder var d f = quote (succ d) (f (var d))


-- Deriving

newtype Quoting t v = Quoting { getQuoting :: v }
