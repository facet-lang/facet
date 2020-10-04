module Facet.Pretty
( hPutDoc
, hPutDocWith
, putDoc
, putDocWith
, toAlpha
, var
, tvar
, varFrom
, tabulate2
, red
, yellow
, green
, cyan
, blue
, magenta
) where

import           Control.Monad.IO.Class
import           Data.Bifunctor (first)
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import           Silkscreen hiding (column, width)
import qualified System.Console.Terminal.Size as Size
import           System.IO (Handle, stdout)

hPutDoc :: MonadIO m => Handle -> PP.Doc ANSI.AnsiStyle -> m ()
hPutDoc handle doc = liftIO $ do
  s <- maybe 80 Size.width <$> Size.size
  ANSI.renderIO handle (PP.layoutSmart PP.defaultLayoutOptions { PP.layoutPageWidth = PP.AvailablePerLine s 0.8 } (doc <> PP.line))

hPutDocWith :: MonadIO m => Handle -> (a -> ANSI.AnsiStyle) -> PP.Doc a -> m ()
hPutDocWith handle style = hPutDoc handle . PP.reAnnotate style

putDoc :: MonadIO m => PP.Doc ANSI.AnsiStyle -> m ()
putDoc = hPutDoc stdout

putDocWith :: MonadIO m => (a -> ANSI.AnsiStyle) -> PP.Doc a -> m ()
putDocWith = hPutDocWith stdout


toAlpha :: String -> Int -> String
toAlpha alphabet i = alphabet !! r : if q > 0 then show q else ""
  where
  n = length alphabet
  (q, r) = i `divMod` n


var :: Printer p => Int -> p
var = varFrom ['a'..'z']

tvar :: Printer p => Int -> p
tvar = varFrom ['A'..'Z']

varFrom :: Printer p => String -> Int -> p
varFrom alpha i = pretty (toAlpha alpha i)


tabulate2 :: PP.Doc ANSI.AnsiStyle -> [(PP.Doc ANSI.AnsiStyle, PP.Doc ANSI.AnsiStyle)] -> PP.Doc ANSI.AnsiStyle
tabulate2 _ [] = mempty
tabulate2 s cs = vsep (map (uncurry entry) cs')
  where entry a b = PP.fill w (doc a) <> s <> b
        w = maximum (map (width . fst) cs')
        cs' = map (first column) cs

data Column = Column { width :: Int, doc :: PP.Doc ANSI.AnsiStyle }

column :: PP.Doc ANSI.AnsiStyle -> Column
column a = Column (length (show (PP.unAnnotate a))) a


red, yellow, green, cyan, blue, magenta :: PP.Doc ANSI.AnsiStyle -> PP.Doc ANSI.AnsiStyle
red     = annotate $ ANSI.color ANSI.Red
yellow  = annotate $ ANSI.color ANSI.Yellow
green   = annotate $ ANSI.color ANSI.Green
cyan    = annotate $ ANSI.color ANSI.Cyan
blue    = annotate $ ANSI.color ANSI.Blue
magenta = annotate $ ANSI.color ANSI.Magenta
