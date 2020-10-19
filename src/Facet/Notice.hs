module Facet.Notice
( -- * Notices
  Notice(..)
, prettyNotice
  -- * Parse errors
, rethrowParseErrors
) where

import qualified Control.Carrier.Parser.Church as Parse
import           Control.Effect.Parser.Notice hiding (prettyNotice)
import           Control.Effect.Parser.Source (Source)
import qualified Facet.Carrier.Throw.Inject as L
import           Facet.Pretty
import           System.Console.ANSI (SGR)

-- Notices

prettyNotice :: Notice [SGR] -> Doc [SGR]
prettyNotice = prettyNoticeWith sgrStyle


-- Parsing

rethrowParseErrors :: L.ThrowC (Notice [SGR]) (Source, Parse.Err) m a -> m a
rethrowParseErrors = L.runThrow (uncurry Parse.errToNotice)
