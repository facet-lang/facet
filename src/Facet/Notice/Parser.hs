module Facet.Notice.Parser
( -- * Parsing
  rethrowParseErrors
) where

import           Data.Maybe (fromMaybe)
import           Data.Set (toList)
import qualified Facet.Carrier.Parser.Church as Parse
import qualified Facet.Carrier.Throw.Inject as L
import           Facet.Notice hiding (Highlight(..))
import           Facet.Source
import           Facet.Span
import           Silkscreen

-- Parsing

rethrowParseErrors :: L.ThrowC (Notice e) (Source, Parse.Err) m a -> m a
rethrowParseErrors = L.runThrow (uncurry errToNotice)


errToNotice :: Source -> Parse.Err -> Notice a
errToNotice source Parse.Err{ Parse.input = Parse.Input pos _, Parse.reason, Parse.expected } = Notice
  { level   = Just Error
  , source  = slice source (Span pos pos)
  , reason  = fillSep (map pretty (words (fromMaybe "unknown error" reason))) <> if null expected then mempty else comma <+> fillSep (pretty "expected" <> colon : punctuate comma (map pretty (toList expected)))
  , context = []
  }
{-# INLINE errToNotice #-}
