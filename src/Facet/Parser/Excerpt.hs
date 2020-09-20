module Facet.Parser.Excerpt
( Excerpt(..)
, excerpted
) where

import Data.Bifunctor (first)
import Facet.Parser.Combinators
import Facet.Parser.Source
import Facet.Parser.Span

data Excerpt = Excerpt
  { excerptPath :: !(Maybe FilePath)
  , excerptLine :: !String
  , excerptSpan :: {-# UNPACK #-} !Span
  }
  deriving (Eq, Ord, Show)

excerpted :: Parsing p => p a -> p (Excerpt, a)
excerpted p = first . mk <$> source <*> spanned p
  where
  mk src span = Excerpt (path src) (src ! start span) span
