module Facet.Style
( terminalNoticeStyle
) where

import Facet.Notice
import Facet.Pretty
import System.Console.ANSI

terminalNoticeStyle :: Highlight [SGR] -> [SGR]
terminalNoticeStyle = \case
  Path      -> [setBold]
  Level l -> case l of
    Warn  -> [SetColor Foreground Vivid Magenta]
    Error -> [SetColor Foreground Vivid Red]
  Span      -> [setBold]
  Reason s  -> s
  Gutter    -> [SetColor Foreground Vivid Blue]
  End       -> [SetColor Foreground Vivid Blue]
  Caret     -> [SetColor Foreground Vivid Green]
  Context s -> s
