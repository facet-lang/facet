{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Effect.Time.System
( -- * Time effect
  now
, timeWith
, timeWith_
, time
, time_
, Time(..)
  -- * Measurements
, Instant(..)
, Duration(..)
, since
  -- * Re-exports
, Algebra
, Has
, run
) where

import           Data.Fixed
import           Data.Time.Clock.System
import           Facet.Effect.Time hiding (now, timeWith, timeWith_)
import qualified Facet.Effect.Time as T

now :: Has (Time Instant) sig m => m Instant
now = T.now
{-# INLINE now #-}

timeWith :: Has (Time Instant) sig m => (Instant -> Instant -> delta) -> m a -> m (delta, a)
timeWith = T.timeWith
{-# INLINE timeWith #-}

timeWith_ :: Has (Time Instant) sig m => (Instant -> Instant -> delta) -> m a -> m delta
timeWith_ = T.timeWith_
{-# INLINE timeWith_ #-}

time :: Has (Time Instant) sig m => m a -> m (Duration, a)
time = timeWith since
{-# INLINE time #-}

time_ :: Has (Time Instant) sig m => m a -> m Duration
time_ = timeWith_ since
{-# INLINE time_ #-}


newtype Instant = Instant { getInstant :: SystemTime }
  deriving (Eq, Ord, Show)

newtype Duration = Duration { getDuration :: Nano }
  deriving (Eq, Fractional, Num, Ord, Real, Show)


since :: Instant -> Instant -> Duration
since (Instant (MkSystemTime bs bns)) (Instant (MkSystemTime as ans)) = Duration (realToFrac (as - bs) + MkFixed (fromIntegral ans - fromIntegral bns))
{-# INLINABLE since #-}
