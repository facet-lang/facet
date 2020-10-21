module Facet.Style
( Style(..)
, terminalNoticeStyle
, terminalCodeStyle
) where

import Data.Colour.RGBSpace.HSL
import Facet.Name (Level(getLevel), Meta(..))
import Facet.Notice as Notice
import Facet.Pretty
import Facet.Print as Print

data Style
  = Notice (Notice.Highlight Style)
  | Code Print.Highlight


terminalNoticeStyle :: Notice.Highlight [SGR] -> [SGR]
terminalNoticeStyle = \case
  Path      -> [setBold]
  Level l -> case l of
    Info  -> [setRGB (hsl 0 0 0.5)]
    Warn  -> [setRGB (hsl 300 1 0.5)]
    Error -> [setRGB (hsl 0 1 0.5)]
  Span      -> [setBold]
  Reason s  -> s
  Gutter    -> [setRGB (hsl 230 1 0.7)]
  End       -> [setRGB (hsl 230 1 0.7)]
  Caret     -> [setRGB (hsl 120 0.8 0.4)]
  Context s -> s

terminalCodeStyle :: Print.Highlight -> [SGR]
terminalCodeStyle = \case
  Nest i -> [setRGB (pick i 0.4 0.8)]
  Name i -> [setRGB (pick (-getLevel i) 0.8 0.6)]
  Op     -> [setRGB (hsl 180 0.7 0.4)]
  Type   -> [setRGB (hsl 60 0.5 0.5)]
  Con    -> [setRGB (hsl 15 0.8 0.5)]
  Lit    -> [setBold]
  Hole m -> [setBold, setRGB (pick (-getMeta m) 0.5 0.45)]
  where
  pick i s l = hsl (fromIntegral i * phi * 30) s l
  phi = 1.618033988749895
