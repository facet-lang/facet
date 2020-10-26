module Facet.Eval
( eval
) where

import Control.Effect.Reader
import Facet.Core
import Facet.Graph
import Facet.Syntax

-- FIXME: erase terms before evaluating.
eval :: (Has (Reader Graph) sig m, Has (Reader Module) sig m) => Value -> m Value
eval = \case
  VNeut h sp -> do
    sp' <- traverse (traverse eval) sp
    mod <- ask
    graph <- ask
    case h of
      Global (q ::: _)
        | Just (_ :=: (Just (DTerm v)) ::: _) <- lookupQ q mod graph
        -> pure $ v $$* sp'
      _ -> pure $ VNeut h sp'

  v          -> pure v
