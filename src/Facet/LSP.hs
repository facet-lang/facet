module Facet.LSP
( lsp
) where

import Data.Default
import Data.IORef
import Data.Text (unpack)
import Facet.Source
import Facet.Span
import Language.Haskell.LSP.Control
import Language.Haskell.LSP.Core
import Language.Haskell.LSP.Messages
import Language.Haskell.LSP.Types
import System.Exit

lsp :: Maybe FilePath -> IO ExitCode
lsp path = do
  sendFuncRef <- newIORef undefined
  let configs = InitializeCallbacks
        { onInitialConfiguration = const (pure ())
        , onConfigurationChange  = const (pure ())
        , onStartup              = \ LspFuncs{ sendFunc } -> do
          Nothing <$ writeIORef sendFuncRef sendFunc
        }
      handlers = def
        { documentSymbolHandler = Just $ \ msg@(RequestMessage _ _ _ (DocumentSymbolParams (TextDocumentIdentifier (Uri text)) _)) -> do
          let path = unpack text
          Source{ span } <- readSourceFromFile path
          let range = fromSpan span
              resp = makeResponseMessage msg (DSDocumentSymbols (List
                [ DocumentSymbol
                  { _name = text
                  , _detail = Nothing
                  , _kind = SkFile
                  , _deprecated = Just False
                  , _range = range
                  , _selectionRange = range
                  , _children = Nothing
                  }
                ]))
          sendFunc <- readIORef sendFuncRef
          sendFunc (RspDocumentSymbols resp)
        }
  exitCode <$> run configs handlers options path
  where
  options = def
  exitCode 0 = ExitSuccess
  exitCode i = ExitFailure i

fromSpan :: Span -> Range
fromSpan (Span s e) = Range (fromPos s) (fromPos e)

fromPos :: Pos -> Position
fromPos (Pos l c) = Position l c
