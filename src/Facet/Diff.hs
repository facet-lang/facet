module Facet.Diff
( applyChange
) where

import           Control.Monad ((<=<))
import qualified Data.IntMap as IntMap
import           Data.Void
import           Facet.Name (Meta(..))
import           Facet.Surface

applyChange :: (Expr Meta, Expr Meta) -> (Expr Void) -> Maybe (Expr Void)
applyChange (d, i) = ins i <=< del d

del :: Expr Meta -> Expr Void -> Maybe (IntMap.IntMap (Expr Void))
del = go IntMap.empty
  where
  go m = curry $ \case
    (Type, Type)             -> pure m
    (Type, _)                -> Nothing
    (TInterface, TInterface) -> pure m
    (TInterface, _)          -> Nothing
    _                        -> Nothing

ins :: Expr Meta -> IntMap.IntMap (Expr Void) -> Maybe (Expr Void)
ins d m = case d of
  M i -> IntMap.lookup (getMeta i) m
  s   -> traverse (const Nothing) s
