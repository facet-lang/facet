{-# LANGUAGE GADTs #-}
module Facet.Effect.Parser
( -- * Parser effect
  Parser(..)
, accept
, position
, spanned
  -- * Re-exports
, Algebra
, Has
, run
) where

import           Control.Algebra
import qualified Facet.Span as Span

data Parser m k where
  Accept     :: (Char -> Maybe a) -> Parser m a
  Label      :: m a -> String ->     Parser m a
  Unexpected :: String ->            Parser m a
  Position   ::                      Parser m Span.Pos

accept :: Has Parser sig m => (Char -> Maybe a) -> m a
accept p = send (Accept p)
{-# INLINE accept #-}

position :: Has Parser sig m => m Span.Pos
position = send Position
{-# INLINE position #-}

spanned :: Has Parser sig m => m a -> m (Span.Span, a)
spanned m = do
  start <- position
  a <- m
  end <- position
  pure (Span.Span start end, a)
{-# INLINE spanned #-}
