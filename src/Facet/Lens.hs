module Facet.Lens
( zoom
, (~>)
, (<~>)
, locally
) where

import Control.Carrier.State.Church
import Control.Effect.Lens (use, (<~))
import Control.Effect.Reader
import Control.Lens (ASetter, Getting, Lens', over)

zoom :: Has (State s) sig m => Lens' s a -> StateC a m () -> m ()
zoom lens action = lens <~> (`execState` action)

infixr 2 `zoom`

-- | Compose a getter onto the input of a Kleisli arrow and run it on the 'State'.
(~>) :: Has (State s) sig m => Getting a s a -> (a -> m b) -> m b
lens ~> act = use lens >>= act

infixr 2 ~>

-- | Compose a lens onto either side of a Kleisli arrow and run it on the 'State'.
(<~>) :: Has (State s) sig m => Lens' s a -> (a -> m a) -> m ()
lens <~> act = lens <~ lens ~> act

infixr 2 <~>


locally :: Has (Reader s) sig m => ASetter s s a b -> (a -> b) -> m r -> m r
locally l f = local (over l f)
