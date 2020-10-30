module Facet.Eval
( Eval(..)
, eval
) where

import Control.Effect.Reader
import Control.Monad (ap, (<=<))
import Control.Monad.Trans.Class
import Facet.Core
import Facet.Graph
import Facet.Syntax

runEval :: (Value -> (Value -> Eval m a) -> m r) -> (a -> m r) -> Eval m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval m a = Eval (forall r . (Value -> (Value -> Eval m a) -> m r) -> (a -> m r) -> m r)

instance Functor (Eval m) where
  fmap f (Eval m) = Eval $ \ hdl k -> m (\ e k -> hdl e (fmap f . k)) (k . f)

instance Applicative (Eval m) where
  pure a = Eval $ \ _ k -> k a
  (<*>) = ap

instance Monad (Eval m) where
  m >>= f = Eval $ \ hdl k -> runEval (\ e k' -> hdl e (f <=< k')) (runEval hdl k . f) m

instance MonadTrans Eval where
  lift m = Eval $ \ _ k -> m >>= k


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
