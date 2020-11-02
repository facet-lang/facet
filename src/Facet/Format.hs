module Facet.Format
( format
) where

import System.Exit

format :: FilePath -> IO ExitCode
format _ = pure ExitSuccess
