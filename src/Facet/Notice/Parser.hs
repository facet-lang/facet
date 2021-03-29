module Facet.Notice.Parser
( -- * Parsing
  rethrowParseErrors
) where

import           Data.Maybe (fromMaybe)
import           Data.Set (toList)
import qualified Facet.Carrier.Parser.Church as Parse
import qualified Facet.Carrier.Throw.Inject as L
import           Facet.Notice
import           Facet.Pretty
import           Facet.Source
import           Facet.Span
import           Silkscreen

-- Parsing

rethrowParseErrors :: Applicative m => L.ThrowC (Notice (Doc e)) (Source, Parse.Err) m a -> m a
rethrowParseErrors = L.runThrow (pure . uncurry errToNotice)


errToNotice :: Source -> Parse.Err -> Notice (Doc a)
errToNotice source Parse.Err{ Parse.input = Parse.Input pos _, Parse.reason, Parse.expected } = Notice
  { level      = Just Error
  , references = [slice source (Span pos pos)]
  , reason     = fillSep (map pretty (words (fromMaybe "unknown error" reason))) <> if null expected then mempty else comma <+> fillSep (pretty "expected" <> colon : punctuate comma (map pretty (toList expected)))
  , context    = []
  }
{-# INLINE errToNotice #-}
