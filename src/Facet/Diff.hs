module Facet.Diff
( applyChange
) where

import           Control.Monad ((<=<))
import qualified Data.IntMap as IntMap
import           Data.Void
import           Facet.Name (Meta(..))
import           Facet.Surface

applyChange :: (Expr Ann Meta, Expr Ann Meta) -> (Expr Ann Void) -> Maybe (Expr Ann Void)
applyChange (d, i) = ins i <=< del d

del :: Expr Ann Meta -> Expr Ann Void -> Maybe (IntMap.IntMap (Expr Ann Void))
del = go IntMap.empty
  where
  go m = curry $ \case
    (Type, Type)             -> pure m
    (Type, _)                -> Nothing
    (TInterface, TInterface) -> pure m
    (TInterface, _)          -> Nothing
    _                        -> Nothing

ins :: Expr Ann Meta -> IntMap.IntMap (Expr Ann Void) -> Maybe (Expr Ann Void)
ins d m = case d of
  M i -> IntMap.lookup (getMeta i) m
  s   -> traverse (const Nothing) s
