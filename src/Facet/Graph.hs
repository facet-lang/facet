module Facet.Graph
( Graph(..)
, insert
, lookup
, GraphErr(..)
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
import           Prelude hiding (lookup)

newtype Graph = Graph { getGraph :: Map.Map MName Module }

insert :: Module -> Graph -> Graph
insert m@Module{ name } = Graph . Map.insert name m . getGraph

lookup :: MName -> Graph -> Maybe Module
lookup n = Map.lookup n . getGraph


data GraphErr
  = CyclicImport (Stack MName)

loadOrder :: Has (Throw GraphErr) sig m => (MName -> m Module) -> [Module] -> m [Module]
loadOrder lookup modules = do
  modules <- execWriter . evalState (Set.empty @MName) . runReader (Nil @MName)
    $ for_ modules visit
  pure $ appEndo modules []
  where
  visit mod@Module{ name, imports } = do
    path <- ask
    when (name `elem` path) $ throwError $ CyclicImport (path :> name)
    seen <- gets (Set.member name)
    unless seen . local (:> name) $ do
      for_ imports $ \ Import{ name } -> do
        mod' <- lift . lift . lift $ lookup name
        visit mod'
      modify (Set.insert name)
      tell (Endo (mod :))
