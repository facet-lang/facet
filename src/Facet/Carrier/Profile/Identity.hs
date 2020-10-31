{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Profile.Identity
( -- * Profiling carrier
  runProfile
, ProfileC(ProfileC)
  -- * Profile effect
, module Facet.Effect.Profile
) where

import Control.Algebra
import Control.Applicative (Alternative)
import Facet.Effect.Profile
import Control.Monad (MonadPlus)
import Control.Monad.Fix
import Control.Monad.IO.Class
import Control.Monad.Trans.Class

newtype ProfileC m a = ProfileC { runProfile :: m a }
  deriving (Alternative, Applicative, Functor, Monad, MonadFail, MonadFix, MonadIO, MonadPlus)

instance MonadTrans ProfileC where
  lift = ProfileC
  {-# INLINE lift #-}

instance Algebra sig m => Algebra (Profile :+: sig) (ProfileC m) where
  alg hdl sig ctx = case sig of
    L (Measure _ m) -> hdl (m <$ ctx)
    R other         -> ProfileC (alg (runProfile . hdl) other ctx)
  {-# INLINE alg #-}
