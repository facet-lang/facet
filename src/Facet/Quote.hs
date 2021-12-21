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
, binderN
) where

import Facet.Name (Level, Used(..))

-- Quotation

-- | @'Quote' v t@ relates (normalized) values in @v@ to terms in @t@.
--
-- Values are expected to have been created by evaluating terms, and as such the properties
--
-- prop> 'quote' 0 . eval 'mempty' = 'id'
-- prop> eval 'mempty' . 'quote' 0 = 'id'
--
-- (i.e. that @'quote'@  is both a left and right inverse of @eval@) should hold for some specific value of @eval@, modulo any effects it performs.
class Quote v t | v -> t where
  -- | Quote a value back to an equivalent term.
  quote
    :: v        -- ^ The value to quote.
    -> Quoter t -- ^ A 'Quoter' producing an equivalent term.

quoteBinder :: Quote v t => Quoter u -> ((u -> v) -> Quoter t)
quoteBinder = quoteBinderWith quote

-- | Quote binding syntax using the given a quotation function.
quoteBinderWith
  :: (v -> Quoter t) -- ^ Quotation of values back to termss.
  -> Quoter u        -- ^ Variable construction.
  -> (u -> v)        -- ^ The higher-order function mapping variables to normalized values.
  -> Quoter t        -- ^ A term representing the position in which the variable is bound.
quoteBinderWith quote var f = Quoter (\ d -> runQuoter (succ d) (quote (f (runQuoter d var))))


class Quote1 v t | v -> t where
  liftQuoteWith :: (u -> Quoter s) -> (v u -> Quoter (t s))

quote1 :: (Quote u s, Quote1 v t) => (v u -> Quoter (t s))
quote1 = liftQuoteWith quote

liftQuoteBinderWith :: Quote1 v t => (u -> Quoter s) -> Quoter r -> ((r -> v u) -> Quoter (t s))
liftQuoteBinderWith = quoteBinderWith . liftQuoteWith


-- Deriving

newtype Quoting t v = Quoting { getQuoting :: v }

instance (Quote v t, Eq t) => Eq (Quoting t v) where
  Quoting a == Quoting b = runQuoter 0 (quote a) == runQuoter 0 (quote b)

instance (Quote v t, Ord t) => Ord (Quoting t v) where
  Quoting a `compare` Quoting b = runQuoter 0 (quote a) `compare` runQuoter 0 (quote b)

instance (Quote v t, Show t) => Show (Quoting t v) where
  showsPrec p = showsPrec p . runQuoter 0 . quote . getQuoting


-- Quoters

-- | 'Quoter' is used to construct first-order representations of syntax directly from higher-order  APIs in final tagless style.
--
-- This typically requires that quotation keep track of the current de Bruijn level, but this data is typically not recorded in ASTs. 'Quoter' instead constructs a function parameterized by the initial level, and thus passing around the current level as quoting proceeds in exactly the same manner as the reader monad.
newtype Quoter a = Quoter (Used -> a)
  deriving (Applicative, Functor, Monad)

runQuoter :: Used -> Quoter a -> a
runQuoter d (Quoter f) = f d

-- | Build quoted first-order syntax from a higher-order representation.
binder
  :: (Level -> Quoter a)    -- ^ Constructor for variables in @a@.
  -> (Quoter a -> Quoter b) -- ^ The binder's scope, represented as a Haskell function mapping variables' values to complete terms.
  -> Quoter b               -- ^ A 'Quoter' of the first-order term.
binder with f = Quoter (\ d -> runQuoter (d + 1) (f (with (getUsed d))))

-- | Build quoted first-order syntax from a higher-order representation taking multiple variables.
binderN
  :: Int
  -> (Level -> Quoter a)      -- ^ Constructor for variables in @a@.
  -> (Quoter [a] -> Quoter b) -- ^ The binder's scope, represented as a Haskell function mapping lists of variables' values to complete terms.
  -> Quoter b                 -- ^ A 'Quoter' of the first-order term.
binderN n with f = Quoter (\ d -> runQuoter (d + n') (f (traverse (with . getUsed) [0..n'])))
  where n' = fromIntegral n
