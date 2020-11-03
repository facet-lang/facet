module Facet.Diff
( applyChange
) where

import           Control.Monad (guard, (<=<))
import qualified Data.IntMap as IntMap
import           Data.Void
import           Facet.Name (Meta(..))
import           Facet.Surface

applyChange :: (Open Expr, Open Expr) -> Closed Expr -> Maybe (Closed Expr)
applyChange (d, i) = ins i <=< del d

type Closed f = f Void
type Open f = f Meta

del :: Open Expr -> Closed Expr -> Maybe (IntMap.IntMap (Closed Expr))
del = go IntMap.empty
  where
  go m = curry $ \case
    (Var n1, Var n2)         -> m <$ guard (n1 == n2)
    (Var{}, _)               -> Nothing
    (Hole n1, Hole n2)       -> m <$ guard (n1 == n2)
    (Hole{}, _)              -> Nothing
    (KType, KType)           -> pure m
    (KType, _)               -> Nothing
    (KInterface, KInterface) -> pure m
    (KInterface, _)          -> Nothing
    (TString, TString)       -> pure m
    (TString, _)             -> Nothing
    (Thunk e1, Thunk e2)     -> goAnn (go m) e1 e2
    (Thunk{}, _)             -> Nothing
    (Force e1, Force e2)     -> goAnn (go m) e1 e2
    (Force{}, _)             -> Nothing
    (App f1 a1, App f2 a2)   -> goAnn (go m) f1 f2 >>= \ m' -> goAnn (go m') a1 a2
    (App{}, _)               -> Nothing
    (As e1 t1, As e2 t2)     -> goAnn (go m) e1 e2 >>= \ m' -> goAnn (go m') t1 t2
    (As{}, _)                -> Nothing
    (String s1, String s2)   -> m <$ guard (s1 == s2)
    -- FIXME: TComp, Lam
    _                        -> Nothing

  goAnn :: (t -> u -> Maybe x) -> Ann t -> Ann u -> Maybe x
  goAnn go (Ann _ c1 e1) (Ann _ c2 e2) = guard (c1 == c2) *> go e1 e2


ins :: Open Expr -> IntMap.IntMap (Closed Expr) -> Maybe (Closed Expr)
ins d _ = traverse (const Nothing) d
