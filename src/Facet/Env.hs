module Facet.Env
( Env(..)
, fromList
, fromModule
, lookup
, lookupQ
, insert
, runEnv
) where

import           Control.Carrier.Reader
import           Control.Monad (guard, (<=<))
import           Data.List (uncons)
import qualified Data.Map as Map
import           Facet.Core
import           Facet.Name
import           Facet.Syntax
import           Prelude hiding (lookup)

newtype Env = Env { getEnv :: Map.Map DName (Map.Map MName Value) }
  deriving (Monoid, Semigroup)

fromList :: [(DName, MName ::: Value)] -> Env
fromList = Env . Map.fromListWith (<>) . map (fmap (\ (mn ::: t) -> Map.singleton mn t))

fromModule :: Module -> Env
fromModule (Module mname _ defs) = fromList $ do
  (dname, def ::: _T) <- defs
  case def of
    DTerm _  -> [ (dname, mname ::: _T) ]
    DData cs ->   (dname, mname ::: _T)
              : [ (C n,   mname ::: _T) | n :=: _ ::: _T <- cs ]

lookup :: DName -> Env -> Maybe (MName ::: Value)
lookup k (Env env) = do
  mod <- Map.lookup k env
  ((mn, v), t) <- uncons (Map.toList mod)
  (mn ::: v) <$ guard (null t)

lookupQ :: QName -> Env -> Maybe Value
lookupQ (m :.: d) = Map.lookup m <=< Map.lookup d . getEnv

insert :: QName ::: Value -> Env -> Env
insert (m :.: d ::: v) = Env . Map.insertWith (<>) d (Map.singleton m v) . getEnv


runEnv :: Has (Reader Module) sig m => ReaderC Env m b -> m b
runEnv m = do
  env <- asks fromModule
  runReader env m
