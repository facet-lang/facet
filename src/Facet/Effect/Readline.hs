{-# LANGUAGE GADTs #-}
module Facet.Effect.Readline
( -- * Readline effect
  Readline(..)
, getInputLine
, getInputLineWithInitial
, getInputChar
, getPassword
, waitForAnyKey
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

getInputLineWithInitial :: Has Readline sig m => String -> (String, String) -> m (Maybe String)
getInputLineWithInitial p lr = send (GetInputLineWithInitial p lr)

getInputChar :: Has Readline sig m => String -> m (Maybe Char)
getInputChar p = send (GetInputChar p)

getPassword :: Has Readline sig m => Maybe Char -> String -> m (Maybe String)
getPassword c s = send (GetPassword c s)

waitForAnyKey :: Has Readline sig m => String -> m Bool
waitForAnyKey p = send (WaitForAnyKey p)

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
  GetInputLineWithInitial :: String -> (String, String) -> Readline m (Maybe String)
  GetInputChar :: String -> Readline m (Maybe Char)
  GetPassword :: Maybe Char -> String -> Readline m (Maybe String)
  WaitForAnyKey :: String -> Readline m Bool
  OutputStr :: String -> Readline m ()
  WithInterrupt :: m a -> Readline m a
  HandleInterrupt :: m a -> m a -> Readline m a
