module Facet.Parser.Excerpt
( Excerpt(..)
, excerpted
) where

import Data.Bifunctor (first)
import Facet.Parser.Combinators
import Facet.Parser.Source as Source
import Facet.Parser.Span

data Excerpt = Excerpt
  { path :: !(Maybe FilePath)
  , line :: !String
  , span :: {-# UNPACK #-} !Span
  }
  deriving (Eq, Ord, Show)

excerpted :: Parsing p => p a -> p (Excerpt, a)
excerpted p = first . mk <$> source <*> spanned p
  where
  mk src span = Excerpt (Source.path src) (src ! start span) span
