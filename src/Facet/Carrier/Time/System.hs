{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Time.System
( -- * Time carrier
  runTime
, TimeC(TimeC)
  -- * Time effect
, module Facet.Effect.Time.System
) where

import Control.Algebra
import Control.Applicative (Alternative)
import Control.Carrier.Lift
import Control.Carrier.Reader
import Control.Monad (MonadPlus)
import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Time.Clock.System
import Facet.Effect.Time.System

runTime :: Has (Lift IO) sig m => TimeC m a -> m a
runTime (TimeC m) = do
  epoch <- Instant <$> sendIO getSystemTime
  runReader epoch m
{-# INLINE runTime #-}

newtype TimeC m a = TimeC { runTimeC :: ReaderC Instant m a }
  deriving (Alternative, Applicative, Functor, Monad, MonadFail, MonadFix, MonadIO, MonadPlus, MonadTrans)

instance Has (Lift IO) sig m => Algebra (Time Instant :+: sig) (TimeC m) where
  alg hdl sig ctx = case sig of
    L Now           -> (<$ ctx) . Instant <$> sendIO getSystemTime
    L Epoch         -> TimeC (asks (<$ ctx))
    L (EraFrom t m) -> TimeC (local (const t) (runTimeC (hdl (m <$ ctx))))
    R other         -> TimeC (alg (runTimeC . hdl) (R other) ctx)
  {-# INLINE alg #-}
