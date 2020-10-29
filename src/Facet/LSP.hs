module Facet.LSP
( lsp
) where

import Data.Default
import Language.Haskell.LSP.Control
import Language.Haskell.LSP.Core
import System.Exit

lsp :: Maybe FilePath -> IO ExitCode
lsp path = exitCode <$> run configs handlers options path
  where
  configs = InitializeCallbacks
    { onInitialConfiguration = const (pure ())
    , onConfigurationChange  = const (pure ())
    , onStartup              = const (pure Nothing)
    }
  handlers = def
  options = def
  exitCode 0 = ExitSuccess
  exitCode i = ExitFailure i
