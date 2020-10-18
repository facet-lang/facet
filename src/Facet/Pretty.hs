{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Pretty
( -- * Output
  layoutOptionsForTerminal
, hPutDoc
, hPutDocWith
, putDoc
, putDocWith
  -- * Helpers
, reflow
  -- * Variable formatting
, toAlpha
, lower
, upper
, varFrom
  -- * Columnar layout
, tabulate2
  -- * Rendering
, renderIO
) where

import           Control.Carrier.Lift
import           Control.Carrier.State.Church
import           Control.Monad.IO.Class
import           Data.Bifunctor (first)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Facet.Stack
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import           Silkscreen hiding (column, width)
import qualified System.Console.ANSI as ANSI
import qualified System.Console.Terminal.Size as Size
import           System.IO (Handle, hPutChar, stdout)

-- Output

layoutOptionsForTerminal :: IO PP.LayoutOptions
layoutOptionsForTerminal = do
  s <- maybe 80 Size.width <$> Size.size
  pure PP.defaultLayoutOptions{ PP.layoutPageWidth = PP.AvailablePerLine s 0.8 }

hPutDoc :: MonadIO m => Handle -> PP.Doc ANSI.AnsiStyle -> m ()
hPutDoc handle doc = liftIO $ do
  opts <- layoutOptionsForTerminal
  ANSI.renderIO handle (PP.layoutSmart opts (doc <> PP.line))

hPutDocWith :: MonadIO m => Handle -> (a -> ANSI.AnsiStyle) -> PP.Doc a -> m ()
hPutDocWith handle style = hPutDoc handle . PP.reAnnotate style

putDoc :: MonadIO m => PP.Doc ANSI.AnsiStyle -> m ()
putDoc = hPutDoc stdout

putDocWith :: MonadIO m => (a -> ANSI.AnsiStyle) -> PP.Doc a -> m ()
putDocWith = hPutDocWith stdout


-- Helpers

reflow :: Printer p => String -> p
reflow = fillSep . map pretty . words


-- Variable formatting

toAlpha :: String -> Int -> String
toAlpha alphabet i = alphabet !! r : if q > 0 then show q else ""
  where
  n = length alphabet
  (q, r) = i `divMod` n


lower :: Printer p => Int -> p
lower = varFrom ['a'..'z']

upper :: Printer p => Int -> p
upper = varFrom ['A'..'Z']

varFrom :: Printer p => String -> Int -> p
varFrom alpha i = pretty (toAlpha alpha i)


-- Columnar layout

tabulate2 :: PP.Doc a -> [(PP.Doc a, PP.Doc a)] -> PP.Doc a
tabulate2 _ [] = mempty
tabulate2 s cs = vsep (map (uncurry entry) cs')
  where entry a b = PP.fill w (doc a) <> s <> b
        w = maximum (map (width . fst) cs')
        cs' = map (first column) cs

data Column a = Column { width :: Int, doc :: PP.Doc a }

column :: PP.Doc a -> Column a
column a = Column (length (show (PP.unAnnotate a))) a


-- Rendering

-- | Render a 'PP.SimpleDocStream' to a 'Handle' using 'ANSI.SGR' codes as the annotation type.
renderIO :: MonadIO m => Handle -> PP.SimpleDocStream [ANSI.SGR] -> m ()
renderIO h stream = do
  let go = \case
        PP.SFail -> error "fail"
        PP.SEmpty -> pure ()
        PP.SChar c rest -> do
            sendM $ hPutChar h c
            go rest
        PP.SText _ t rest -> do
            sendM $ T.hPutStr h t
            go rest
        PP.SLine i rest -> do
            sendM $ hPutChar h '\n'
            sendM $ T.hPutStr h (T.replicate i (T.singleton ' '))
            go rest
        PP.SAnnPush style rest -> do
            currentStyle <- unsafePeek
            let newStyle = style <> currentStyle
            push newStyle
            sendM $ ANSI.setSGR newStyle
            go rest
        PP.SAnnPop rest -> do
            _currentStyle <- unsafePop
            newStyle <- unsafePeek
            sendM $ ANSI.setSGR newStyle
            go rest
  liftIO $ runM $ evalState (Nil :: Stack [ANSI.SGR]) $ go stream
  where
  push x = modify (:>x)
  unsafePeek = do
    _ :> l <- get
    pure l
  unsafePop = do
    i :> _ <- get
    put (i :: Stack [ANSI.SGR])
