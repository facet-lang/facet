module Facet.Graph
( Graph(..)
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

loadOrder :: Has (Throw (Stack MName)) sig m => (MName -> Graph -> m Module) -> Graph -> m [Module]
loadOrder lookup graph = do
  modules <- execWriter . evalState (Set.empty @MName) . runReader (Nil @MName)
    $ for_ (Map.toList (getGraph graph)) (uncurry visit)
  pure $ appEndo modules []
  where
  visit mname mod = do
    path <- ask
    when (mname `elem` path) $ throwError (path :> mname)
    seen <- gets (Set.member mname)
    unless seen . local (:> mname) $ do
      for_ (imports mod) $ \ (Import mname') -> do
        mod' <- lift . lift . lift $ lookup mname' graph
        visit mname' mod'
      modify (Set.insert mname)
      tell (Endo (mod :))
