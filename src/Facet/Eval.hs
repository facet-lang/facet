{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Eval
( Eval(..)
, eval
, eval0
) where

import Control.Applicative (liftA, liftA2)
import Control.Monad (ap, (<=<))
import Data.Bool (bool)
import Facet.Expr

newtype Eval sig a = Eval { runEval :: forall r . (Eff sig (Eval sig a) -> r) -> (a -> r) -> r }

eval :: (Eff sig (Eval sig a) -> r) -> (a -> r) -> Eval sig a -> r
eval h k e = runEval e h k

eval0 :: (a -> r) -> Eval None a -> r
eval0 = eval absurdE

instance Functor (Eval sig) where
  fmap = liftA

instance Applicative (Eval sig) where
  pure a = Eval $ \ _ k -> k a

  (<*>) = ap

instance Monad (Eval sig) where
  m >>= f = Eval $ \ h k -> eval (\ (Eff e k') -> h (Eff e (f <=< k'))) (eval h k . f) m

instance Expr Eval where
  val = pure . eval0 id

  lam f = pure go
    where
    go a = Eval $ \ hb kb -> eval
      (\ (Eff e k') -> case e of
        InL eff -> eval hb kb (f (Right (Eff eff k')))
        InR sig -> hb (Eff sig (go . k')))
      (eval hb kb . f . Left . pure)
      a

  f $$ a = Eval $ \ h k -> runEval f (\ (Eff e k') -> h (Eff e (($$ a) . k'))) $ \ f' -> runEval (f' a) h k

  inlr = liftA2 (,)

  inl = fmap Left
  inr = fmap Right
  exlr f g e = e >>= either (f . pure) (g . pure)

  true  = pure True
  false = pure False
  iff c t e = c >>= bool e t

  alg e = Eval $ \ h _ -> h e

  weaken e = Eval $ \ h k -> eval (\ (Eff e k') -> h (Eff (InR e) (weaken . k'))) k e
