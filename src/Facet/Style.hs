module Facet.Style
( terminalNoticeStyle
) where

import Data.Colour.RGBSpace.HSL
import Facet.Notice
import Facet.Pretty

terminalNoticeStyle :: Highlight [SGR] -> [SGR]
terminalNoticeStyle = \case
  Path      -> [setBold]
  Level l -> case l of
    Warn  -> [setRGB (hsl 300 1 0.5)]
    Error -> [setRGB (hsl 0 1 0.5)]
  Span      -> [setBold]
  Reason s  -> s
  Gutter    -> [setRGB (hsl 230 1 0.7)]
  End       -> [setRGB (hsl 230 1 0.7)]
  Caret     -> [setRGB (hsl 120 0.8 0.4)]
  Context s -> s
