{-# LANGUAGE TypeFamilies #-}
-- FIXME: redefine this as a tree w/ qualifiers operating as paths
module Facet.Graph
( Graph(..)
, singleton
, restrict
, insert
, lookupM
, lookupWith
, lookupQ
, GraphErr(..)
, Node(..)
, loadOrder
) where

import           Control.Applicative (Alternative(..))
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Carrier.Writer.Church
import           Control.Effect.Throw
import           Control.Lens as Lens (At(..), Index, IxValue, Ixed(..), iso)
import           Control.Monad (guard, unless, when, (<=<))
import           Control.Monad.Trans.Class
import           Data.Foldable (asum, for_)
import qualified Data.Map as Map
import           Data.Monoid (Endo(..))
import qualified Data.Set as Set
import           Facet.Core.Module
import           Facet.Core.Type hiding (insert)
import           Facet.Name
import           Facet.Snoc
import           Facet.Syntax

newtype Graph = Graph { getGraph :: Map.Map MName (Maybe FilePath, Maybe Module) }
  deriving (Semigroup, Monoid)

type instance Lens.Index Graph = MName
type instance IxValue Graph = (Maybe FilePath, Maybe Module)

instance Ixed Graph
instance At   Graph where
  at i = iso getGraph Graph .at i

singleton :: Maybe FilePath -> Module -> Graph
singleton p m@Module{ name } = Graph (Map.singleton name (p, Just m))

restrict :: Graph -> Set.Set MName -> Graph
restrict (Graph g) s = Graph $ Map.restrictKeys g s

insert :: Maybe FilePath -> Module -> Graph -> Graph
insert p m@Module{ name } = Graph . Map.insert name (p, Just m) . getGraph

lookupM :: Alternative m => MName -> Graph -> m (Maybe FilePath, Maybe Module)
lookupM n = maybe empty pure . Map.lookup n . getGraph

lookupWith :: (Alternative m, Monad m) => (Name -> Module -> m res) -> Graph -> Module -> QName -> m res
lookupWith lookup graph mod@Module{ name } (m:.:n)
  =   guard (m == name || m == Nil) *> lookup n mod
  <|> guard (m == Nil) *> asum (maybe empty (lookup n) . snd <$> getGraph graph)
  <|> guard (m /= Nil) *> (lookupM m graph >>= maybe empty pure . snd >>= lookup n)

lookupQ :: (Alternative m, Monad m) => Graph -> Module -> QName -> m (QName :=: Maybe Def ::: Type)
lookupQ = lookupWith lookupD


-- FIXME: enrich this with source references for each
newtype GraphErr = CyclicImport (Snoc MName)

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
