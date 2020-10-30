module Facet.Carrier.Output.IO
( -- * Output carrier
  runOutput
, OutputC(OutputC)
  -- * Output effect
, module Facet.Effect.Readline
) where

import Facet.Effect.Readline

newtype OutputC m a = OutputC { runOutput :: m a }
