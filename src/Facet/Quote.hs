{-# LANGUAGE FunctionalDependencies #-}
module Facet.Quote
( -- * Quotation
  Quote(..)
) where

import Facet.Name (Level)

-- Quotation

class Quote v t | v -> t where
  quote :: Level -> v -> t
