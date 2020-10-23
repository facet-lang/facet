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
import           Control.Effect.State
import           Control.Monad (guard, (<=<))
import           Data.List (uncons)
import qualified Data.Map as Map
import           Facet.Core
import           Facet.Name
import           Facet.Syntax
import           Prelude hiding (lookup)

newtype Env = Env { getEnv :: Map.Map DName (Map.Map MName (Maybe Value ::: Value)) }
  deriving (Monoid, Semigroup)

fromList :: [(DName, MName :=: Maybe Value ::: Value)] -> Env
fromList = Env . Map.fromListWith (<>) . map (fmap (\ (mn :=: t) -> Map.singleton mn t))

fromModule :: Module -> Env
fromModule (Module mname _ defs) = fromList $ do
  (dname, def ::: _T) <- defs
  case def of
    DTerm v  -> [ (dname, mname :=: Just v ::: _T) ]
    DData cs ->   (dname, mname :=: Nothing ::: _T)
              : [ (C n,   mname :=: Just v ::: _T) | n :=: v ::: _T <- cs ]

lookup :: DName -> Env -> Maybe (MName :=: Maybe Value ::: Value)
lookup k (Env env) = do
  mod <- Map.lookup k env
  ((mn, v), t) <- uncons (Map.toList mod)
  (mn :=: v) <$ guard (null t)

lookupQ :: QName -> Env -> Maybe (Maybe Value ::: Value)
lookupQ (m :.: d) = Map.lookup m <=< Map.lookup d . getEnv

insert :: QName :=: Maybe Value ::: Value -> Env -> Env
insert (m :.: d :=: v) = Env . Map.insertWith (<>) d (Map.singleton m v) . getEnv


runEnv :: Has (State (Env)) sig m => ReaderC (Env) m b -> m b
runEnv m = do
  env <- get
  runReader env m
