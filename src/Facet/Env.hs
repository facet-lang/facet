module Facet.Env
( Env(..)
, fromList
, fromModule
, lookupD
, lookupQ
, insert
, runEnv
) where

import           Control.Carrier.Reader
import           Control.Monad (guard, (<=<))
import           Data.List (uncons)
import qualified Data.Map as Map
import           Facet.Core hiding (lookupD)
import qualified Facet.Graph as G
import           Facet.Name
import           Facet.Syntax

newtype Env = Env { getEnv :: Map.Map DName (Map.Map MName Value) }
  deriving (Monoid, Semigroup)

fromList :: [(DName, MName ::: Value)] -> Env
fromList = Env . Map.fromListWith (<>) . map (fmap (\ (mn ::: t) -> Map.singleton mn t))

fromModule :: Module -> G.Graph -> Env
fromModule m@(Module _ is _) g = fromList $ local m ++ imported
  where
  local (Module mname _ defs) = do
    (dname, def ::: _T) <- defs
    case def of
      DTerm _  -> [ (dname, mname ::: _T) ]
      DData cs ->   (dname, mname ::: _T)
                : [ (C n,   mname ::: _T) | n :=: _ ::: _T <- cs ]
  imported = do
    Import{ name } <- is
    (_, m) <- G.lookupM name g
    exported m
  -- FIXME: there needs to be some mechanism for exporting (or not exporting) local definitions from a module
  exported = local


lookupD :: DName -> Env -> Maybe (MName ::: Value)
lookupD k (Env env) = do
  mod <- Map.lookup k env
  ((mn, v), t) <- uncons (Map.toList mod)
  (mn ::: v) <$ guard (null t)

lookupQ :: QName -> Env -> Maybe Value
lookupQ (m :.: d) = Map.lookup m <=< Map.lookup d . getEnv

insert :: QName ::: Value -> Env -> Env
insert (m :.: d ::: v) = Env . Map.insertWith (<>) d (Map.singleton m v) . getEnv


runEnv :: (Has (Reader G.Graph) sig m, Has (Reader Module) sig m) => ReaderC Env m b -> m b
runEnv m = do
  env <- fromModule <$> ask <*> ask
  runReader env m
