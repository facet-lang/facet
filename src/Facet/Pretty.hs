module Facet.Pretty
( -- * Output
  layoutOptionsForHandle
, hPutDoc
, hPutDocWith
, putDoc
, putDocWith
  -- * Helpers
, reflow
, unlines
, (<\>)
  -- * Variable formatting
, toAlpha
, lower
, upper
, varFrom
, subscript
, subscriptWith
, digits
  -- * Columnar layout
, tabulate2
  -- * Rendering
, renderIO
, renderLazy
  -- * ANSI codes
, setRGB
, setRGBBack
, setBold
  -- * Re-exports
, PP.Doc
, PP.Pretty
, pretty
, PP.layoutSmart
, SGR
) where

import           Control.Carrier.Lift
import           Control.Carrier.State.Church
import           Control.Monad.IO.Class
import           Data.Bifunctor (first)
import           Data.Colour.RGBSpace
import           Data.Colour.SRGB
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Builder as TLB
import           Facet.Snoc
import           Prelude hiding (unlines)
import qualified Prettyprinter as PP
import           Silkscreen hiding (column, width)
import           System.Console.ANSI
import qualified System.Console.Terminal.Size as Size
import           System.IO (Handle, hPutChar, stdout)

-- Output

layoutOptionsForHandle :: Handle -> IO PP.LayoutOptions
layoutOptionsForHandle hdl = do
  s <- maybe 80 Size.width <$> Size.hSize hdl
  pure PP.defaultLayoutOptions{ PP.layoutPageWidth = PP.AvailablePerLine s 1 }

hPutDoc :: MonadIO m => Handle -> PP.Doc [SGR] -> m ()
hPutDoc handle = hPutDocWith handle id

hPutDocWith :: MonadIO m => Handle -> (a -> [SGR]) -> PP.Doc a -> m ()
hPutDocWith handle style doc = liftIO $ do
  opts <- layoutOptionsForHandle handle
  renderIO handle (PP.reAnnotateS style (PP.layoutSmart opts doc))

putDoc :: MonadIO m => PP.Doc [SGR] -> m ()
putDoc = hPutDoc stdout

putDocWith :: MonadIO m => (a -> [SGR]) -> PP.Doc a -> m ()
putDocWith = hPutDocWith stdout


-- Helpers

reflow :: Printer p => String -> p
reflow = fillSep . map pretty . words

unlines :: Printer p => [p] -> p
unlines = concatWith (<\>)

(<\>) :: Printer p => p -> p -> p
(<\>) = surround hardline


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


subscript :: Printer p => Int -> p
subscript i = sign <> foldMap (pretty . (subscripts !!) . abs) (digits i)
  where
  sign | i < 0     = pretty "₋"
       | otherwise = mempty
  subscripts = ['₀'..'₉']

subscriptWith :: (s -> s -> s) -> (Char -> s) -> s -> Int -> s
subscriptWith (<>) pretty mempty i = sign <> foldr ((<>) . pretty . (subscripts !!) . abs) mempty (digits i)
  where
  sign | i < 0     = pretty '₋'
       | otherwise = mempty
  subscripts = ['₀'..'₉']

digits :: Int -> [Int]
digits = go []
  where
  go ds i
    | abs i < 10 = i:ds
    | otherwise  = let (q, r) = i `quotRem` 10 in go (r:ds) q


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

-- | Render a 'PP.SimpleDocStream' to a 'Handle' using 'SGR' codes as the annotation type.
renderIO :: MonadIO m => Handle -> PP.SimpleDocStream [SGR] -> m ()
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
            sendM $ setSGR newStyle
            go rest
        PP.SAnnPop rest -> do
            _currentStyle <- unsafePop
            newStyle <- unsafePeek
            sendM $ setSGR newStyle
            go rest
  liftIO $ runM $ evalState (Nil :> ([] :: [SGR])) $ go stream
  where
  push x = modify (:>x)
  unsafePeek = do
    _ :> l <- get
    pure l
  unsafePop = do
    i :> _ <- get
    put (i :: Snoc [SGR])

renderLazy :: PP.SimpleDocStream [SGR] -> TL.Text
renderLazy =
  let push x = (:>x)

      unsafePeek Nil    = error "peeking an empty stack"
      unsafePeek (_:>x) = x

      unsafePop Nil     = error "popping an empty stack"
      unsafePop (xs:>x) = (x, xs)

      go :: Snoc [SGR] -> PP.SimpleDocStream [SGR] -> TLB.Builder
      go s sds = case sds of
        PP.SFail -> error "fail"
        PP.SEmpty -> mempty
        PP.SChar c rest -> TLB.singleton c <> go s rest
        PP.SText _ t rest -> TLB.fromText t <> go s rest
        PP.SLine i rest -> TLB.singleton '\n' <> TLB.fromText (T.replicate i (T.pack " ")) <> go s rest
        PP.SAnnPush style rest ->
            let currentStyle = unsafePeek s
                newStyle = style <> currentStyle
            in  TLB.fromText (T.pack (setSGRCode newStyle)) <> go (push style s) rest
        PP.SAnnPop rest ->
            let (_currentStyle, s') = unsafePop s
                newStyle = unsafePeek s'
            in  TLB.fromText (T.pack (setSGRCode newStyle)) <> go s' rest

  in TLB.toLazyText . go (Nil :> [])


-- ANSI codes

setRGB :: RGB Float -> SGR
setRGB = SetRGBColor Foreground . uncurryRGB sRGB

setRGBBack :: RGB Float -> SGR
setRGBBack = SetRGBColor Background . uncurryRGB sRGB

setBold :: SGR
setBold = SetConsoleIntensity BoldIntensity
