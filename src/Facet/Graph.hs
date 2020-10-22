{-# LANGUAGE ScopedTypeVariables #-}
module Facet.Graph
( Graph(..)
, Node(..)
, loadOrder
) where

import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Carrier.Writer.Church
import           Control.Effect.Throw
import           Control.Monad (unless, when)
import           Control.Monad.Trans.Class
import           Data.Foldable (for_)
import qualified Data.Map as Map
import           Data.Monoid (Endo(..))
import qualified Data.Set as Set
import           Facet.Core
import           Facet.Name
import           Facet.Stack

newtype Graph = Graph { getGraph :: Map.Map MName Module }

data Node k v = Node k [k] v

loadOrder :: (Has (Throw (Stack k)) sig m, Ord k) => (k -> m (Node k v)) -> [Node k v] -> m [Node k v]
loadOrder (lookup :: k -> m (Node k v)) modules = do
  modules <- execWriter . evalState (Set.empty @k) . runReader (Nil @k)
    $ for_ modules visit
  pure $ appEndo modules []
  where
  visit mod@(Node name edges _) = do
    path <- ask
    when (name `elem` path) $ throwError (path :> name)
    seen <- gets (Set.member name)
    unless seen . local (:> name) $ do
      for_ edges $ \ name' -> do
        mod' <- lift . lift . lift $ lookup name'
        visit mod'
      modify (Set.insert name)
      tell (Endo (mod :))
