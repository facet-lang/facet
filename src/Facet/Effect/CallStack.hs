{-# LANGUAGE GADTs #-}
module Facet.Effect.CallStack
( pushCallStack
, CallStack(..)
) where

import           Control.Algebra
import           Data.Text (Text)
import qualified Facet.Span as Span

pushCallStack :: Has CallStack sig m => Text -> Span.Span -> m a -> m a
pushCallStack l s m = send (Push l s m)

data CallStack m a where
  Push :: Text -> Span.Span -> m a -> CallStack m a
