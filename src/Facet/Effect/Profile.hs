{-# LANGUAGE GADTs #-}
module Facet.Effect.Profile
( -- * Profile effect
  measure
, Profile(..)
  -- * Re-exports
, Algebra
, Has
, run
) where

import Control.Algebra
import Data.Text

measure :: Has Profile sig m => Text -> m a -> m a
measure l m = send (Measure l m)
{-# INLINE measure #-}

data Profile m k where
  Measure :: Text -> m a -> Profile m a
