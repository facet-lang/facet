module Facet.Eval
( Eval(..)
, eval
) where

import Control.Effect.Reader
import Facet.Core
import Facet.Graph
import Facet.Syntax

newtype Eval m a = Eval { runEval :: forall r . (Value -> (Value -> Eval m a) -> m r) -> (a -> m r) -> m r }

instance Functor (Eval m) where
  fmap f (Eval m) = Eval $ \ hdl k -> m (\ e k -> hdl e (fmap f . k)) (k . f)


-- FIXME: erase terms before evaluating.
eval :: (Has (Reader Graph) sig m, Has (Reader Module) sig m) => Value -> m Value
eval = \case
  VNeut h sp -> do
    sp' <- traverse (traverse eval) sp
    mod <- ask
    graph <- ask
    case h of
      Global q
        | Just (_ :=: Just (DTerm v) ::: _) <- lookupQ q mod graph
        -> eval $ v $$* sp'
      _ -> pure $ VNeut h sp'

  VComp (Comp [] v) -> eval v

  v          -> pure v
