{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Carrier.Fail.Throw.Print
( FailC(..)
) where

import Control.Monad.Fix

newtype FailC p m a = FailC { runFail :: m a }
  deriving (Applicative, Functor, Monad, MonadFix)
