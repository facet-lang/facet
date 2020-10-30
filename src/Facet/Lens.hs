module Facet.Lens
( zoom
, (~>)
, (<~>)
) where

import Control.Carrier.State.Church
import Control.Effect.Lens (use, (<~))
import Control.Lens (Getting, Lens')

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
