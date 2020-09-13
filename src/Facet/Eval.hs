{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
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

newtype Eval sig a = Eval { runEval :: forall r . (forall k . sig k -> (k -> Eval sig a) -> r) -> (a -> r) -> r }

eval :: (forall k . sig k -> (k -> Eval sig a) -> r) -> (a -> r) -> Eval sig a -> r
eval h k e = runEval e h k

eval0 :: (a -> r) -> Eval None a -> r
eval0 = eval (\case{})

instance Functor (Eval sig) where
  fmap = liftA

instance Applicative (Eval sig) where
  pure a = Eval $ \ _ k -> k a

  (<*>) = ap

instance Monad (Eval sig) where
  m >>= f = Eval $ \ h k -> eval (\ e k' -> h e (f <=< k')) (eval h k . f) m

instance Expr Eval where
  val = pure . eval0 id

  lam f = pure go
    where
    go a = Eval $ \ hb kb -> eval
      (\case
        InL eff -> eval hb kb . f . Right . Eff eff
        InR sig -> \ k' -> hb sig (go . k'))
      (eval hb kb . f . Left . pure)
      a

  f $$ a = Eval $ \ h k -> runEval f (\ e k' -> h e (($$ a) . k')) $ \ f' -> runEval (f' a) h k

  unit = pure ()

  inlr = liftA2 (,)
  exl = fmap fst
  exr = fmap snd

  inl = fmap Left
  inr = fmap Right
  exlr f g e = e >>= either (f . pure) (g . pure)

  true  = pure True
  false = pure False
  iff c t e = c >>= bool e t

  alg (Eff e k) = Eval $ \ h _ -> h e k

  weaken e = Eval $ \ h k -> eval (\ e k' -> h (InR e) (weaken . k')) k e
