module Facet.Style
( Style(..)
, terminalStyle
, terminalNoticeStyle
, terminalCodeStyle
  -- * Pretty-printing
, prettyNotice'
, prettyCode
) where

import           Data.Colour.RGBSpace.HSL
import           Facet.Name (Level(getLevel), Meta(..))
import qualified Facet.Notice as Notice
import           Facet.Pretty
import           Facet.Print as Print
import qualified Prettyprinter as P

data Style
  = Failure
  | Success
  | Progress
  | Command
  | Notice (Notice.Highlight Style)
  | Code Print.Highlight


terminalStyle :: Style -> [SGR]
terminalStyle = \case
  Failure  -> [setRGB (hsl 0 1 0.5)]
  Success  -> [setRGB (hsl 120 1 0.5)]
  Progress -> [setRGB (hsl 0 0 0.5), setBold]
  Command  -> [setRGB (hsl 180 1 0.5)]
  Notice n -> terminalNoticeStyle (fmap terminalStyle n)
  Code s   -> terminalCodeStyle s

terminalNoticeStyle :: Notice.Highlight [SGR] -> [SGR]
terminalNoticeStyle = \case
  Notice.Path      -> [setBold]
  Notice.Level l -> case l of
    Notice.Info  -> [setRGB (hsl 0 0 0.5)]
    Notice.Warn  -> [setRGB (hsl 300 1 0.5)]
    Notice.Error -> [setRGB (hsl 0 1 0.5)]
  Notice.Span      -> [setBold]
  Notice.Reason s  -> s
  Notice.Gutter    -> [setRGB (hsl 230 1 0.7)]
  Notice.End       -> [setRGB (hsl 230 1 0.7)]
  Notice.Caret     -> [setRGB (hsl 120 0.8 0.4)]
  Notice.Context s -> s

terminalCodeStyle :: Print.Highlight -> [SGR]
terminalCodeStyle = \case
  Nest i  -> [setRGB (pick i 0.4 0.8)]
  Name i  -> [setRGB (pick (-getLevel i) 0.8 0.6)]
  Keyword -> [setRGB (hsl 300 0.7 0.4)]
  Op      -> [setRGB (hsl 180 0.7 0.4)]
  Type    -> [setRGB (hsl 60 0.5 0.5)]
  Con     -> [setRGB (hsl 15 0.8 0.5)]
  Lit     -> [setBold]
  Hole m  -> [setBold, setRGB (pick (-getMeta m) 0.5 0.45)]
  where
  pick i s l = hsl (fromIntegral i * phi * 30) s l
  phi = 1.618033988749895


-- Pretty-printing

prettyNotice' :: Notice.Notice Style -> Doc Style
prettyNotice' = P.reAnnotate Notice . Notice.prettyNotice

prettyCode :: Print -> Doc Style
prettyCode = P.reAnnotate Code . getPrint
