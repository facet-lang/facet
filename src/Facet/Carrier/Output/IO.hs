module Facet.Carrier.Output.IO
( -- * Output carrier
  runOutput
, OutputC(OutputC)
  -- * Output effect
, module Facet.Effect.Readline
) where

import Control.Monad.Fix
import Control.Monad.IO.Class
import Facet.Effect.Readline

newtype OutputC m a = OutputC { runOutput :: m a }
  deriving (Applicative, Functor, Monad, MonadFail, MonadFix, MonadIO)
