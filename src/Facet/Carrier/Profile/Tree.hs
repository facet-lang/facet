{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Profile.Tree
( -- * Profile carrier
  runProfile
, reportProfile
, execProfile
, ProfileC(ProfileC)
  -- * Profile effect
, module Facet.Effect.Profile
  -- * Timings
, module Facet.Timing
) where

import Control.Algebra
import Control.Applicative (Alternative)
import Control.Carrier.Writer.Church
import Control.Monad (MonadPlus)
import Control.Monad.Fix
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Facet.Effect.Profile
import Facet.Effect.Time.System
import Facet.Timing

runProfile :: Applicative m => ProfileC m a -> m (Timings, a)
runProfile = runWriter (curry pure) . runProfileC
{-# INLINE runProfile #-}

reportProfile :: MonadIO m => ProfileC m a -> m a
reportProfile m = do
  (t, a) <- runProfile m
  a <$ reportTimings t
{-# INLINE reportProfile #-}

execProfile :: Applicative m => ProfileC m a -> m Timings
execProfile = execWriter . runProfileC
{-# INLINE execProfile #-}

newtype ProfileC m a = ProfileC { runProfileC :: WriterC Timings m a }
  deriving (Alternative, Applicative, Functor, Monad, MonadFail, MonadFix, MonadIO, MonadPlus, MonadTrans)

instance Has (Time Instant) sig m => Algebra (Profile :+: sig) (ProfileC m) where
  alg hdl sig ctx = case sig of
    L (Measure l m) -> do
      (sub, (duration, a)) <- ProfileC (censor @Timings (const mempty) (listen (runProfileC (time (hdl (m <$ ctx))))))
      a <$ ProfileC (tell (singleton l duration sub))
    R other         -> ProfileC (alg (runProfileC . hdl) (R other) ctx)
  {-# INLINE alg #-}
