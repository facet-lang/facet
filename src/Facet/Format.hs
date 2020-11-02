module Facet.Format
( format
) where

import System.Exit

-- FIXME: allow module names w/ search paths
format :: [FilePath] -> FilePath -> IO ExitCode
format _ _ = pure ExitSuccess
