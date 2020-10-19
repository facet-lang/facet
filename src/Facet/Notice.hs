module Facet.Notice
( Notice(..)
, prettyNotice
) where

import Control.Effect.Parser.Notice hiding (prettyNotice)
import Facet.Pretty
import Prettyprinter (Doc)
import System.Console.ANSI (SGR)

prettyNotice :: Notice [SGR] -> Doc [SGR]
prettyNotice = prettyNoticeWith sgrStyle
