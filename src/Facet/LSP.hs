module Facet.LSP
( lsp
) where

import Data.Default
import Language.Haskell.LSP.Control
import Language.Haskell.LSP.Core

lsp :: Maybe FilePath -> IO Int
lsp = run configs handlers options
  where
  configs = InitializeCallbacks
    { onInitialConfiguration = const (pure ())
    , onConfigurationChange  = const (pure ())
    , onStartup              = const (pure Nothing)
    }
  handlers = def
  options = def
