{-# LANGUAGE GADTs #-}
module Facet.Effect.Parser
( -- * Parser effect
  Parser(..)
, accept
, position
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
