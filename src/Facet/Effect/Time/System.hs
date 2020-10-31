{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Effect.Time.System
( -- * Time effect
  now
, timeWith
, time
, epoch
, sinceEpochWith
, sinceEpoch
, eraFrom
, era
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
import           Facet.Effect.Time hiding (epoch, eraFrom, now, sinceEpochWith, timeWith)
import qualified Facet.Effect.Time as T

now :: Has (Time Instant) sig m => m Instant
now = T.now
{-# INLINE now #-}

timeWith :: Has (Time Instant) sig m => (Instant -> Instant -> delta) -> m a -> m (delta, a)
timeWith = T.timeWith
{-# INLINE timeWith #-}

time :: Has (Time Instant) sig m => m a -> m (Duration, a)
time = timeWith since
{-# INLINE time #-}

epoch :: Has (Time Instant) sig m => m Instant
epoch = T.epoch
{-# INLINE epoch #-}

sinceEpochWith :: Has (Time Instant) sig m => (Instant -> Instant -> delta) -> m delta
sinceEpochWith = T.sinceEpochWith
{-# INLINE sinceEpochWith #-}

sinceEpoch :: Has (Time Instant) sig m => m Duration
sinceEpoch = sinceEpochWith since
{-# INLINE sinceEpoch #-}

eraFrom :: Has (Time Instant) sig m => Instant -> m a -> m a
eraFrom = T.eraFrom
{-# INLINE eraFrom #-}

era :: Has (Time Instant) sig m => m a -> m a
era m = do
  epoch <- now
  eraFrom epoch m
{-# INLINE era #-}


newtype Instant = Instant { getInstant :: SystemTime }
  deriving (Eq, Ord, Show)

newtype Duration = Duration { getDuration :: Nano }
  deriving (Eq, Fractional, Num, Ord, Real, Show)


since :: Instant -> Instant -> Duration
since (Instant (MkSystemTime bs bns)) (Instant (MkSystemTime as ans)) = Duration (realToFrac (as - bs) + MkFixed (fromIntegral ans - fromIntegral bns))
{-# INLINABLE since #-}
