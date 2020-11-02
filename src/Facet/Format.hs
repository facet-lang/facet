module Facet.Format
( format
) where

import System.Exit

-- FIXME: allow module names w/ search paths
-- FIXME: it really sucks that we have to have search paths and parse everything to be able to work on this one file
format :: [FilePath] -> FilePath -> IO ExitCode
format _ _ = pure ExitSuccess
