module Facet.Graph
( Node(..)
, loadOrder
) where

import           Control.Carrier.Reader
import           Control.Carrier.State.Church
import           Control.Carrier.Writer.Church
import           Control.Effect.Throw
import           Control.Monad (unless, when)
import           Control.Monad.Trans.Class
import           Data.Foldable (for_)
import           Data.Monoid (Endo(..))
import qualified Data.Set as Set
import           Facet.Stack

data Node k v = Node k [k] v

loadOrder :: (Has (Throw (Stack k)) sig m, Ord k) => (k -> m (Node k v)) -> [Node k v] -> m [Node k v]
loadOrder lookup modules = do
  modules <- runTraversal $ for_ modules visit
  pure $ appEndo modules []
  where
  runTraversal :: Applicative m => ReaderC (Stack k) (StateC (Set.Set k) (WriterC (Endo [Node k v]) m)) a -> m (Endo [Node k v])
  runTraversal = execWriter . evalState Set.empty . runReader Nil
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
