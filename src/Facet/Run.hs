module Facet.Run
( runFile
) where

import System.Exit

runFile :: FilePath -> IO ExitCode
runFile _ = do
  pure ExitSuccess
