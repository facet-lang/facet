module Facet.Run
( runFile
) where

import System.Exit

runFile :: [FilePath] -> FilePath -> IO ExitCode
runFile _ _ = pure ExitSuccess
