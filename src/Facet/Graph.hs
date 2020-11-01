{-# LANGUAGE TypeFamilies #-}
module Facet.Graph
( Graph(..)
, singleton
, restrict
, insert
, lookupM
, lookupQ
, GraphErr(..)
, Node(..)
, loadOrder
) where

import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Carrier.Writer.Church
import           Control.Effect.Empty
import           Control.Effect.Throw
import           Control.Lens as Lens (At(..), Index, IxValue, Ixed(..), iso)
import           Control.Monad (unless, when, (<=<))
import           Control.Monad.Trans.Class
import           Data.Foldable (for_)
import qualified Data.Map as Map
import           Data.Monoid (Endo(..))
import qualified Data.Set as Set
import           Facet.Core
import           Facet.Name
import           Facet.Stack
import           Facet.Syntax

newtype Graph = Graph { getGraph :: Map.Map MName (Maybe FilePath, Module) }
  deriving (Semigroup, Monoid)

type instance Lens.Index Graph = MName
type instance IxValue Graph = (Maybe FilePath, Module)

instance Ixed Graph
instance At   Graph where
  at i = iso getGraph Graph .at i

singleton :: Maybe FilePath -> Module -> Graph
singleton p m@Module{ name } = Graph (Map.singleton name (p, m))

restrict :: Graph -> Set.Set MName -> Graph
restrict (Graph g) s = Graph $ Map.restrictKeys g s

insert :: Maybe FilePath -> Module -> Graph -> Graph
insert p m@Module{ name } = Graph . Map.insert name (p, m) . getGraph

lookupM :: Has Empty sig m => MName -> Graph -> m (Maybe FilePath, Module)
lookupM n = maybe empty pure . Map.lookup n . getGraph

lookupQ :: Has Empty sig m => QName -> Module -> Graph -> m (QName :=: Maybe Def ::: Comp)
lookupQ (m:.:n) mod@Module{ name } g
  | m == name = lookupD n mod
  -- FIXME: produce multiple results for a module, if they exist.
  | otherwise = lookupM m g >>= lookupD n . snd


-- FIXME: enrich this with source references for each
newtype GraphErr = CyclicImport (Stack MName)

data Node a = Node MName [MName] a

loadOrder :: Has (Throw GraphErr) sig m => (MName -> m (Node a)) -> [Node a] -> m [a]
loadOrder lookup modules = do
  modules <- execWriter . evalState (Set.empty @MName) . runReader (Nil @MName)
    $ for_ modules visit
  pure $ appEndo modules []
  where
  visit (Node name edges mod) = do
    path <- ask
    when (name `elem` path) $ throwError $ CyclicImport (path :> name)
    seen <- gets (Set.member name)
    unless seen . local (:> name) $ do
      for_ edges edge
      modify (Set.insert name)
      tell (Endo (mod :))
  edge = visit <=< lift . lift . lift . lookup
