{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.State.Lens
( -- * State carrier
  runState
, StateC(..)
  -- * State effect
, module Control.Effect.State
) where

import Control.Algebra
import Control.Carrier.Reader
import Control.Effect.State
import Control.Monad.IO.Class
import Fresnel.Getter ((^.))
import Fresnel.Lens (Lens')
import Fresnel.Setter (set)

runState :: Lens' s t -> StateC s t m a -> m a
runState lens (StateC m) = runReader (ALens' lens) m
{-# INLINE runState #-}

newtype StateC s t m a = StateC (ReaderC (ALens' s t) m a)
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)

instance Has (State s) sig m => Algebra (State t :+: sig) (StateC s t m) where
  alg hdl sig ctx = StateC $ ReaderC $ \ (ALens' lens) -> case sig of
    L Get     -> (<$ ctx) <$> gets (^. lens)
    L (Put s) -> (<$ ctx) <$> modify (set lens s)
    R other   -> alg (runState lens . hdl) other ctx
  {-# INLINABLE alg #-}


newtype ALens' s a = ALens' (Lens' s a)
