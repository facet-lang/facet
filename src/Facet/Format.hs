module Facet.Format
( format
) where

import System.Exit

-- FIXME: allow module names w/ search paths
format :: FilePath -> IO ExitCode
format _ = pure ExitSuccess
