module Facet.Source.Reference
( Reference(..)
) where

import qualified Facet.Span as Span

data Reference = Reference
  { path :: Maybe FilePath
  , span :: Span.Span
  }
