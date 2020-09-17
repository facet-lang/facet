{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Eval
( Eval(..)
, eval
, eval0
) where

import Control.Monad (ap, liftM)
import Facet.Expr

newtype Eval sig a = Eval { runEval :: forall r . (Inst sig (Eval sig a) -> r) -> (a -> r) -> r }

eval :: (Inst sig (Eval sig a) -> r) -> (a -> r) -> Eval sig a -> r
eval h k e = runEval e h k

eval0 :: (a -> r) -> Eval None a -> r
eval0 = eval absurdI

instance Functor (Eval sig) where
  fmap = liftM

instance Applicative (Eval sig) where
  pure a = Eval $ \ _ k -> k a

  (<*>) = ap

instance Monad (Eval sig) where
  m >>= f = Eval $ \ h k -> eval (\ e -> h ((>>= f) <$> e)) (eval h k . f) m

instance Expr Eval where
  lam f = pure go
    where
    go a = Eval $ \ hb kb -> eval
      (\ (Inst e k') -> case e of
        InL eff -> eval hb kb (f (Right (Inst eff k')))
        InR sig -> hb (Inst sig (go . k')))
      (eval hb kb . f . Left . pure)
      a

  f $$ a = Eval $ \ h k -> runEval f (\ e -> h (($$ a) <$> e)) $ \ f' -> runEval (f' a) h k

  alg e k = Eval $ \ h _ -> h (Inst e k)

  weakenBy f = go where go e = Eval $ \ h k -> eval (\ (Inst e k') -> h (Inst (f e) (go . k'))) k e
