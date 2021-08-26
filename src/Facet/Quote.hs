{-# LANGUAGE FunctionalDependencies #-}
module Facet.Quote
( -- * Quotation
  Quote(..)
, quoteBinder
, quoteBinderWith
, Quote1(..)
, quote1
, liftQuoteBinderWith
  -- * Deriving
, Quoting(..)
  -- * Quoters
, Quoter(..)
, runQuoter
, binder
) where

import Facet.Name (Level, Used(..))

-- Quotation

class Quote v t | v -> t where
  quote :: Used -> v -> t

quoteBinder :: Quote v t => (Used -> u) -> Used -> (u -> v) -> t
quoteBinder = quoteBinderWith quote

quoteBinderWith :: (Used -> v -> t) -> (Used -> u) -> Used -> (u -> v) -> t
quoteBinderWith quote var d f = quote (succ d) (f (var d))


class Quote1 v t | v -> t where
  liftQuoteWith :: (Used -> u -> s) -> Used -> v u -> t s

quote1 :: (Quote u s, Quote1 v t) => Used -> v u -> t s
quote1 = liftQuoteWith quote

liftQuoteBinderWith :: Quote1 v t => (Used -> u -> s) -> (Used -> r) -> Used -> (r -> v u) -> t s
liftQuoteBinderWith = quoteBinderWith . liftQuoteWith


-- Deriving

newtype Quoting t v = Quoting { getQuoting :: v }

instance (Quote v t, Eq t) => Eq (Quoting t v) where
  Quoting a == Quoting b = quote 0 a == quote 0 b

instance (Quote v t, Ord t) => Ord (Quoting t v) where
  Quoting a `compare` Quoting b = quote 0 a `compare` quote 0 b

instance (Quote v t, Show t) => Show (Quoting t v) where
  showsPrec p = showsPrec p . quote 0 . getQuoting


-- Quoters

newtype Quoter a = Quoter (Used -> a)
  deriving (Applicative, Functor, Monad)

runQuoter :: Used -> Quoter a -> a
runQuoter d (Quoter f) = f d

binder :: (Used -> Level -> a) -> (Quoter a -> Quoter b) -> Quoter b
binder with f = Quoter (\ d -> runQuoter (d + 1) (f (Quoter (`with` getUsed d))))
