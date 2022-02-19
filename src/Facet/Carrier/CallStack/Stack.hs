module Facet.Carrier.CallStack.Stack
( CallStackC(..)
) where

import           Control.Carrier.State.Church
import qualified Data.Text as Text
import qualified Facet.Span as Span

newtype CallStackC m a = CallStackC (StateC [(Text.Text, Span.Span)] m a)
