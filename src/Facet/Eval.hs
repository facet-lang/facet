module Facet.Eval
( runEval
, Eval(..)
, eval
) where

import Control.Effect.Reader
import Control.Monad.Trans.Class
import Facet.Core
import Facet.Graph
import Facet.Name
import Facet.Syntax

runEval :: (QName :$ (Pl, Value) -> (Value -> m r) -> m r) -> (a -> m r) -> Eval m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval m a = Eval (forall r . (QName :$ (Pl, Value) -> (Value -> m r) -> m r) -> (a -> m r) -> m r)

instance Functor (Eval m) where
  fmap f (Eval m) = Eval $ \ hdl k -> m hdl (k . f)

instance Applicative (Eval m) where
  pure a = Eval $ \ _ k -> k a
  f <*> a = Eval $ \ hdl k -> runEval hdl (\ f' -> runEval hdl (\ a' -> k $! f' a') a) f

instance Monad (Eval m) where
  m >>= f = Eval $ \ hdl k -> runEval hdl (runEval hdl k . f) m

instance MonadTrans Eval where
  lift m = Eval $ \ _ k -> m >>= k


-- FIXME: erase terms before evaluating.
eval :: (Has (Reader Graph) sig m, Has (Reader Module) sig m) => Value -> Eval m Value
eval = \case
  VNe (h :$ sp) -> do
    sp' <- traverse (traverse eval) sp
    mod <- lift ask
    graph <- lift ask
    case h of
      Global q
        | Just (_ :=: Just (DTerm v) ::: _) <- lookupQ q mod graph
        -> eval $ v $$* sp'
      _ -> pure $ VNe (h :$ sp')

  TSusp (Comp Nothing v) -> eval v

  EOp op -> Eval $ \ h -> h op

  v          -> pure v
