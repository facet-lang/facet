{-# LANGUAGE GADTs #-}
module Facet.Effect.Readline
( -- * Readline effect
  Readline(..)
, getInputLine
, outputStr
, outputStrLn
, withInterrupt
, handleInterrupt
  -- * Re-exports
, Algebra
, Has
, run
) where

import Control.Algebra

getInputLine :: Has Readline sig m => String -> m (Maybe String)
getInputLine p = send (GetInputLine p)

outputStr :: Has Readline sig m => String -> m ()
outputStr s = send (OutputStr s)

outputStrLn :: Has Readline sig m => String -> m ()
outputStrLn s = outputStr (s <> "\n")

withInterrupt :: Has Readline sig m => m a -> m a
withInterrupt m = send (WithInterrupt m)

handleInterrupt :: Has Readline sig m => m a -> m a -> m a
handleInterrupt h m = send (HandleInterrupt h m)

data Readline m k where
  GetInputLine :: String -> Readline m (Maybe String)
  OutputStr :: String -> Readline m ()
  WithInterrupt :: m a -> Readline m a
  HandleInterrupt :: m a -> m a -> Readline m a
