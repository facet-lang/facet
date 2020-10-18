{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
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
, toSGR
, renderIO
, renderLazy
) where

import           Control.Carrier.Lift
import           Control.Carrier.State.Church
import           Control.Monad.IO.Class
import           Data.Bifunctor (first)
import           Data.Maybe (catMaybes)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Builder as TLB
import           Facet.Stack
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as PP
import qualified Prettyprinter.Render.Terminal.Internal as PPI
import           Silkscreen hiding (column, width)
import qualified System.Console.ANSI as ANSI
import qualified System.Console.Terminal.Size as Size
import           System.IO (Handle, hPutChar, stdout)

-- Output

layoutOptionsForTerminal :: IO PP.LayoutOptions
layoutOptionsForTerminal = do
  s <- maybe 80 Size.width <$> Size.size
  pure PP.defaultLayoutOptions{ PP.layoutPageWidth = PP.AvailablePerLine s 0.8 }

hPutDoc :: MonadIO m => Handle -> PP.Doc PP.AnsiStyle -> m ()
hPutDoc handle doc = liftIO $ do
  opts <- layoutOptionsForTerminal
  PP.renderIO handle (PP.layoutSmart opts (doc <> PP.line))

hPutDocWith :: MonadIO m => Handle -> (a -> PP.AnsiStyle) -> PP.Doc a -> m ()
hPutDocWith handle style = hPutDoc handle . PP.reAnnotate style

putDoc :: MonadIO m => PP.Doc PP.AnsiStyle -> m ()
putDoc = hPutDoc stdout

putDocWith :: MonadIO m => (a -> PP.AnsiStyle) -> PP.Doc a -> m ()
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

toSGR :: PPI.AnsiStyle -> [ANSI.SGR]
toSGR (PPI.SetAnsiStyle{ PPI.ansiBold, PPI.ansiForeground }) = catMaybes
  [ ANSI.SetConsoleIntensity ANSI.BoldIntensity <$ ansiBold
  , (\ (i, c) -> ANSI.SetColor ANSI.Foreground (intensity i) (colour c)) <$> ansiForeground
  ]
  where
  intensity = \case
    PPI.Dull  -> ANSI.Dull
    PPI.Vivid -> ANSI.Vivid
  colour = \case
    PPI.Black   -> ANSI.Black
    PPI.Red     -> ANSI.Red
    PPI.Green   -> ANSI.Green
    PPI.Yellow  -> ANSI.Yellow
    PPI.Blue    -> ANSI.Blue
    PPI.Magenta -> ANSI.Magenta
    PPI.Cyan    -> ANSI.Cyan
    PPI.White   -> ANSI.White

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
  liftIO $ runM $ evalState (Nil :> ([] :: [ANSI.SGR])) $ go stream
  where
  push x = modify (:>x)
  unsafePeek = do
    _ :> l <- get
    pure l
  unsafePop = do
    i :> _ <- get
    put (i :: Stack [ANSI.SGR])

renderLazy :: PP.SimpleDocStream [ANSI.SGR] -> TL.Text
renderLazy =
  let push x = (:>x)

      unsafePeek Nil    = error "peeking an empty stack"
      unsafePeek (_:>x) = x

      unsafePop Nil     = error "popping an empty stack"
      unsafePop (xs:>x) = (x, xs)

      go :: Stack [ANSI.SGR] -> PP.SimpleDocStream [ANSI.SGR] -> TLB.Builder
      go s sds = case sds of
        PP.SFail -> error "fail"
        PP.SEmpty -> mempty
        PP.SChar c rest -> TLB.singleton c <> go s rest
        PP.SText _ t rest -> TLB.fromText t <> go s rest
        PP.SLine i rest -> TLB.singleton '\n' <> TLB.fromText (T.replicate i (T.pack " ")) <> go s rest
        PP.SAnnPush style rest ->
            let currentStyle = unsafePeek s
                newStyle = style <> currentStyle
            in  TLB.fromText (T.pack (ANSI.setSGRCode newStyle)) <> go (push style s) rest
        PP.SAnnPop rest ->
            let (_currentStyle, s') = unsafePop s
                newStyle = unsafePeek s'
            in  TLB.fromText (T.pack (ANSI.setSGRCode newStyle)) <> go s' rest

  in TLB.toLazyText . go (Nil :> [])
