{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.CallStack.Stack
( -- * CallStack carrier
  CallStackC(..)
  -- * CallStack effect
, module Facet.Effect.CallStack
) where

import Control.Algebra
import Control.Carrier.Reader
import Facet.Effect.CallStack

newtype CallStackC m a = CallStackC { runCallStackC :: ReaderC Stack m a }
  deriving (Applicative, Functor, Monad)

instance Algebra sig m => Algebra (CallStack :+: sig) (CallStackC m) where
  alg hdl sig ctx = CallStackC $ case sig of
    L (Push l s m) -> local ((l, s):) (runCallStackC (hdl (m <$ ctx)))
    L CallStack    -> asks (<$ ctx)
    R other        -> alg (runCallStackC . hdl) (R other) ctx
