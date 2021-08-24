{-# LANGUAGE TypeFamilies #-}
module Facet.Lens
( zoom
, (<~)
, (~>)
, (<~>)
, locally
, use
, uses
, view
, views
, (%=)
, (.=)
, modifying
, assign
, At(..)
, Ixed(..)
, ixAt
) where

import           Control.Carrier.State.Church
import           Control.Effect.Reader
import qualified Data.Map as Map
import           Data.Profunctor.Traversing (wander)
import qualified Fresnel.Getter as Getter
import qualified Fresnel.Lens as Lens
import qualified Fresnel.Setter as Setter
import qualified Fresnel.Traversal as Traversal

zoom :: Has (State s) sig m => Lens.Lens' s a -> StateC a m () -> m ()
zoom lens action = lens <~> (`execState` action)

infixr 2 `zoom`

(<~) :: Has (State s) sig m => Setter.Setter s s a b -> m b -> m ()
o <~ m = m >>= assign o

-- | Compose a getter onto the input of a Kleisli arrow and run it on the 'State'.
(~>) :: Has (State s) sig m => Getter.Getter s a -> (a -> m b) -> m b
lens ~> act = use lens >>= act

infixr 2 <~, ~>, <~>

-- | Compose a lens onto either side of a Kleisli arrow and run it on the 'State'.
(<~>) :: Has (State s) sig m => Lens.Lens' s a -> (a -> m a) -> m ()
lens <~> act = lens <~ lens ~> act


locally :: Has (Reader s) sig m => Setter.Setter s s a b -> (a -> b) -> m r -> m r
locally o = local . Setter.over o


use :: Has (State s) sig m => Getter.Getter s a -> m a
use o = gets (Getter.view o)

uses :: Has (State s) sig m => Getter.Getter s a -> (a -> b) -> m b
uses o f = f <$> use o

view :: Has (Reader s) sig m => Getter.Getter s a -> m a
view o = asks (Getter.view o)

views :: Has (Reader s) sig m => Getter.Getter s a -> (a -> b) -> m b
views o f = f <$> view o

(%=) :: Has (State s) sig m => Setter.Setter s s a b -> (a -> b) -> m ()
(%=) = modifying

infix 4 %=, .=

(.=) :: Has (State s) sig m => Setter.Setter s s a b -> b -> m ()
(.=) = assign

modifying :: Has (State s) sig m => Setter.Setter s s a b -> (a -> b) -> m ()
modifying o = modify . Setter.over o

assign :: Has (State s) sig m => Setter.Setter s s a b -> b -> m ()
assign o = modify . Setter.set o


class Ixed a where
  type Index a
  type IxValue a

  ix :: Index a -> Traversal.Traversal' a (IxValue a)

instance Ord k => Ixed (Map.Map k v) where
  type Index (Map.Map k v) = k
  type IxValue (Map.Map k v) = v
  ix k = wander $ \ f m -> case Map.lookup k m of
    Just v  -> fmap (\ v' -> Map.insert k v' m) (f v)
    Nothing -> pure m


class Ixed a => At a where
  at :: Index a -> Lens.Lens' a (Maybe (IxValue a))

instance Ord k => At (Map.Map k v) where
  at k = Lens.lens (Map.lookup k) (\ m v -> maybe (Map.delete k m) (\ v -> Map.insert k v m) v)


ixAt :: At a => Index a -> Traversal.Traversal' a (IxValue a)
ixAt i = at i . wander traverse
