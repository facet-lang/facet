module Facet.Env
( Env(..)
, fromModule
, lookupD
, lookupQ
, insert
, runEnv
) where

import           Control.Carrier.Reader hiding (local)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Facet.Core hiding (lookupD)
import qualified Facet.Graph as G
import           Facet.Name
import           Facet.Syntax

data Env = Env { mname :: MName, local :: Map.Map DName Value, imports :: G.Graph }

fromModule :: Module -> G.Graph -> Env
fromModule m@(Module mname is _) g = Env mname (Map.fromList (local m)) (G.restrict g (Set.fromList (map (\ Import{ name } -> name) is)))
  where
  local (Module _ _ defs) = do
    (dname, def ::: _T) <- defs
    (dname, _T) : case def of
      Just (DData cs) -> [ (C n,   _T) | n :=: _ ::: _T <- cs ]
      _               -> []


lookupD :: DName -> Env -> Maybe (MName ::: Value)
lookupD k (Env mn local _) = (mn :::) <$> Map.lookup k local

lookupQ :: QName -> Env -> Maybe Value
lookupQ q@(m :.: d) e@(Env m' _ g)
  | m == m'   = ty <$> lookupD d e
  | otherwise = ty <$> G.lookupQ q (Module (MName mempty) [] []) g

insert :: DName ::: Value -> Env -> Env
insert (d ::: v) e = e{ local = Map.insert d v (local e) }


runEnv :: (Has (Reader G.Graph) sig m, Has (Reader Module) sig m) => ReaderC Env m b -> m b
runEnv m = do
  env <- fromModule <$> ask <*> ask
  runReader env m
