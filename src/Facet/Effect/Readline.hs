{-# LANGUAGE GADTs #-}
-- FIXME: split this into separate input and output effect modules.
module Facet.Effect.Readline
( -- * Input effect
  Input(..)
, getInputLine
, withInterrupt
, handleInterrupt
  -- * Output effect
, Output(..)
, outputStr
, outputStrLn
, outputText
, outputTextLn
, outputDoc
, outputDocLn
  -- * Re-exports
, Algebra
, Has
, run
) where

import Control.Algebra
import Data.Kind (Type)
import Data.Text
import Facet.Pretty
import Facet.Style
import Prettyprinter (hardline)

getInputLine :: Has Input sig m => String -> m (Maybe String)
getInputLine p = send (GetInputLine p)

withInterrupt :: Has Input sig m => m a -> m a
withInterrupt m = send (WithInterrupt m)

handleInterrupt :: Has Input sig m => m a -> m a -> m a
handleInterrupt h m = send (HandleInterrupt h m)

data Input m k where
  GetInputLine :: String -> Input m (Maybe String)
  WithInterrupt :: m a -> Input m a
  HandleInterrupt :: m a -> m a -> Input m a


outputStr :: Has Output sig m => String -> m ()
outputStr s = outputDoc (pretty s)

outputStrLn :: Has Output sig m => String -> m ()
outputStrLn s = outputDocLn (pretty s)

outputText :: Has Output sig m => Text -> m ()
outputText s = outputDoc (pretty s)

outputTextLn :: Has Output sig m => Text -> m ()
outputTextLn s = outputDocLn (pretty s)

outputDoc :: Has Output sig m => Doc Style -> m ()
outputDoc s = send (OutputDoc s)

outputDocLn :: Has Output sig m => Doc Style -> m ()
outputDocLn s = outputDoc s *> outputDoc hardline

data Output (m :: Type -> Type) k where
  OutputDoc :: Doc Style -> Output m ()
