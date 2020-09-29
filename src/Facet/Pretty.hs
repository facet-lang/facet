module Facet.Pretty
( hPutDoc
, hPutDocWith
, putDoc
, putDocWith
, toAlpha
, var
, tvar
, varFrom
) where

import           Control.Monad.IO.Class
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import           Silkscreen
import           System.Console.Terminal.Size as Size
import           System.IO (Handle, stdout)

hPutDoc :: MonadIO m => Handle -> PP.Doc ANSI.AnsiStyle -> m ()
hPutDoc handle doc = liftIO $ do
  s <- maybe 80 Size.width <$> size
  ANSI.renderIO handle (PP.layoutSmart PP.defaultLayoutOptions { PP.layoutPageWidth = PP.AvailablePerLine s 0.8 } (doc <> PP.line))

hPutDocWith :: MonadIO m => Handle -> (a -> ANSI.AnsiStyle) -> PP.Doc a -> m ()
hPutDocWith handle style = hPutDoc handle . PP.reAnnotate style

putDoc :: MonadIO m => PP.Doc ANSI.AnsiStyle -> m ()
putDoc = hPutDoc stdout

putDocWith :: MonadIO m => (a -> ANSI.AnsiStyle) -> PP.Doc a -> m ()
putDocWith style = putDoc . PP.reAnnotate style


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
