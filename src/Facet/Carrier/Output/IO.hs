{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Output.IO
( -- * Output carrier
  runOutput
, OutputC(OutputC)
  -- * Output effect
, module Facet.Effect.Readline
) where

import Control.Algebra
import Control.Monad.Fix
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Facet.Effect.Readline
import Facet.Pretty (putDocWith)
import Facet.Style (terminalStyle)

newtype OutputC m a = OutputC { runOutput :: m a }
  deriving (Applicative, Functor, Monad, MonadFail, MonadFix, MonadIO)

instance MonadTrans OutputC where
  lift = OutputC

instance (Algebra sig m, MonadIO m) => Algebra (Output :+: sig) (OutputC m) where
  alg hdl sig ctx = case sig of
    L (OutputDoc d) -> (<$ ctx) <$> putDocWith terminalStyle d
    R other         -> OutputC $ alg (runOutput . hdl) other ctx
