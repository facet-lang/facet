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

import           Control.Algebra
import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Carrier.Writer.Church
import           Control.Effect.Choose
import           Control.Effect.Empty
import           Control.Effect.Throw
import           Control.Monad (unless, when, (<=<))
import           Control.Monad.Trans.Class
import           Data.Foldable (for_)
import qualified Data.Map as Map
import           Data.Monoid (Endo(..))
import qualified Data.Set as Set
import           Facet.Module
import           Facet.Name
import           Facet.Snoc
import           Facet.Snoc.NonEmpty (NonEmpty(..), fromSnoc, toSnoc)
import           Facet.Syntax
import           Fresnel.At
import           Fresnel.Iso
import           Fresnel.Ixed

newtype Graph = Graph { getGraph :: Map.Map QName (Maybe FilePath, Maybe Module) }
  deriving (Monoid, Semigroup)

instance Ixed Graph where
  type Index Graph = QName
  type IxValue Graph = (Maybe FilePath, Maybe Module)
  ix = ixAt

instance At   Graph where
  at i = iso getGraph Graph .at i

singleton :: Maybe FilePath -> Module -> Graph
singleton p m@Module{ name } = Graph (Map.singleton name (p, Just m))

restrict :: Graph -> Set.Set QName -> Graph
restrict (Graph g) s = Graph $ Map.restrictKeys g s

insert :: Maybe FilePath -> Module -> Graph -> Graph
insert p m@Module{ name } = Graph . Map.insert name (p, Just m) . getGraph

lookupM :: Has (Choose :+: Empty) sig m => QName -> Graph -> m (Maybe FilePath, Maybe Module)
lookupM n = maybe empty pure . Map.lookup n . getGraph

lookupWith :: Has (Choose :+: Empty) sig m => (Name -> Module -> m res) -> Graph -> Module -> QName -> m res
lookupWith lookup graph mod@Module{ name } (m:|>n)
  =   guard (m == toSnoc name || m == Nil) *> lookup n mod
  <|> guard (m == Nil) *> foldMapC (maybe empty (lookup n) . snd) (getGraph graph)
  <|> guard (m /= Nil) *> (lookupM (fromSnoc m) graph >>= maybe empty pure . snd >>= lookup n)

lookupQ :: Has (Choose :+: Empty) sig m => Graph -> Module -> QName -> m (QName :=: Def)
lookupQ = lookupWith lookupDef


-- FIXME: enrich this with source references for each
newtype GraphErr = CyclicImport (Snoc QName)

data Node a = Node QName [QName] a

loadOrder :: Has (Throw GraphErr) sig m => (QName -> m (Node a)) -> [Node a] -> m [a]
loadOrder lookup modules = do
  modules <- execWriter . evalState (Set.empty @QName) . runReader (Nil @QName)
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
