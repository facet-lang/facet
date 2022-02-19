module Facet.Carrier.CallStack.Stack
( CallStackC(..)
) where

import           Control.Carrier.Reader
import qualified Data.Text as Text
import qualified Facet.Span as Span

newtype CallStackC m a = CallStackC { runCallStackC :: ReaderC [(Text.Text, Span.Span)] m a }
  deriving (Applicative, Functor, Monad)
