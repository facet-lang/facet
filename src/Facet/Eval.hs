{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Eval
( Eval(..)
, eval
, eval0
) where

import Control.Monad (ap, liftM, (<=<))
import Facet.Expr

newtype Eval sig a = Eval { runEval :: forall r . (Eff sig (Eval sig a) -> r) -> (a -> r) -> r }

eval :: (Eff sig (Eval sig a) -> r) -> (a -> r) -> Eval sig a -> r
eval h k e = runEval e h k

eval0 :: (a -> r) -> Eval None a -> r
eval0 = eval absurdE

instance Functor (Eval sig) where
  fmap = liftM

instance Applicative (Eval sig) where
  pure a = Eval $ \ _ k -> k a

  (<*>) = ap

instance Monad (Eval sig) where
  m >>= f = Eval $ \ h k -> eval (\ (Eff e k') -> h (Eff e (f <=< k'))) (eval h k . f) m

instance Expr Eval where
  lam f = pure go
    where
    go a = Eval $ \ hb kb -> eval
      (\ (Eff e k') -> case e of
        InL eff -> eval hb kb (f (Right (Eff eff k')))
        InR sig -> hb (Eff sig (go . k')))
      (eval hb kb . f . Left . pure)
      a

  f $$ a = Eval $ \ h k -> runEval f (\ (Eff e k') -> h (Eff e (($$ a) . k'))) $ \ f' -> runEval (f' a) h k

  alg e = Eval $ \ h _ -> h e

  weakenBy f = go where go e = Eval $ \ h k -> eval (\ (Eff e k') -> h (Eff (f e) (go . k'))) k e
