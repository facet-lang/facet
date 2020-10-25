{-# LANGUAGE GADTs #-}
module Facet.Effect.Readline
( -- * Readline effect
  Readline(..)
, getInputLine
, outputStr
, outputStrLn
, outputDoc
, outputDocLn
, withInterrupt
, handleInterrupt
  -- * Re-exports
, Algebra
, Has
, run
) where

import Control.Algebra
import Facet.Pretty
import Facet.Style

getInputLine :: Has Readline sig m => String -> m (Maybe String)
getInputLine p = send (GetInputLine p)

outputStr :: Has Readline sig m => String -> m ()
outputStr s = outputDoc (pretty s)

outputStrLn :: Has Readline sig m => String -> m ()
outputStrLn s = outputStr (s <> "\n")

outputDoc :: Has Readline sig m => Doc Style -> m ()
outputDoc s = send (OutputDoc s)

outputDocLn :: Has Readline sig m => Doc Style -> m ()
outputDocLn s = outputDoc (s <> pretty "\n")

withInterrupt :: Has Readline sig m => m a -> m a
withInterrupt m = send (WithInterrupt m)

handleInterrupt :: Has Readline sig m => m a -> m a -> m a
handleInterrupt h m = send (HandleInterrupt h m)

-- FIXME: split into separate input and output effects
data Readline m k where
  GetInputLine :: String -> Readline m (Maybe String)
  OutputDoc :: Doc Style -> Readline m ()
  WithInterrupt :: m a -> Readline m a
  HandleInterrupt :: m a -> m a -> Readline m a
