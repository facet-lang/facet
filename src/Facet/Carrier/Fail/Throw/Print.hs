{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Fail.Throw.Print
( FailC(..)
) where

import Control.Algebra
import Control.Effect.Fail
import Control.Effect.Throw
import Control.Monad.Fix
import Silkscreen

newtype FailC p m a = FailC { runFail :: m a }
  deriving (Applicative, Functor, Monad, MonadFix)

instance (Has (Throw p) sig m, Printer p) => MonadFail (FailC p m) where
  fail = FailC . throwError @p . pretty

instance (Has (Throw p) sig m, Printer p) => Algebra (Fail :+: sig) (FailC p m) where
  alg hdl sig ctx = case sig of
    L (Fail s) -> fail s
    R sig      -> FailC (alg (runFail . hdl) sig ctx)
