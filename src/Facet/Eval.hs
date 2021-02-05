module Facet.Eval
( -- * Evaluation
  Value(..)
, eval
  -- * Machinery
, runEval
, Eval(..)
) where

import Control.Algebra
import Control.Effect.Reader
import Control.Monad.Trans.Class
import Facet.Core.Module
import Facet.Core.Term hiding (eval)
import Facet.Core.Type (Type)
import Facet.Graph
import Facet.Name
import Facet.Stack
import Facet.Syntax

eval :: Has (Reader Graph :+: Reader Module) sig m => Value -> Eval m Value
eval = \case
  VNe h ts sp  -> do
    sp' <- traverse eval sp
    mod <- lift ask
    graph <- lift ask
    case h of
      Global (lookupQ graph mod -> Just (_ :=: Just (DTerm v) ::: _))
        -> eval $ v $$$* ts $$* sp'
      _ -> pure $ VNe h ts sp'

  VOp op ts as -> Eval $ \ h -> h op ts as

  v            -> pure v


-- Machinery

runEval :: (Q Name -> Stack Type -> Stack Value -> (Value -> m r) -> m r) -> (a -> m r) -> Eval m a -> m r
runEval hdl k (Eval m) = m hdl k

newtype Eval m a = Eval (forall r . (Q Name -> Stack Type -> Stack Value -> (Value -> m r) -> m r) -> (a -> m r) -> m r)

instance Functor (Eval m) where
  fmap f (Eval m) = Eval $ \ hdl k -> m hdl (k . f)

instance Applicative (Eval m) where
  pure a = Eval $ \ _ k -> k a
  f <*> a = Eval $ \ hdl k -> runEval hdl (\ f' -> runEval hdl (\ a' -> k $! f' a') a) f

instance Monad (Eval m) where
  m >>= f = Eval $ \ hdl k -> runEval hdl (runEval hdl k . f) m

instance MonadTrans Eval where
  lift m = Eval $ \ _ k -> m >>= k
