{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Eval
( Eval(..)
, eval
, eval0
, Handler(..)
, handle
) where

import Control.Applicative (liftA, liftA2)
import Data.Bool (bool)
import Data.Kind (Type)
import Facet.Expr

newtype Eval (sig :: Type -> Type) a = Eval { runEval :: forall r . Handler None r -> (a -> r) -> r }

eval :: Handler None r -> (a -> r) -> Eval sig a -> r
eval h k e = runEval e h k

eval0 :: Eval None a -> a
eval0 = eval (Handler (const . absurd)) id

instance Functor (Eval sig) where
  fmap = liftA

instance Applicative (Eval sig) where
  pure a = Eval $ \ _ k -> k a

  f <*> a = Eval $ \ h k -> runEval f h (\ f' -> runEval a h (k . f'))

instance Monad (Eval sig) where
  m >>= f = Eval $ \ h k -> runEval m h (eval h k . f)

instance Expr Eval where
  val = pure . eval0

  -- not using the incoming handler indicates that we don’t need to perform effects to construct the lambda itself, even if it uses effects to do its job
  lam f = Eval $ \ _ k -> k (eval (Handler (const . absurd)) (f . Left . pure))
  f $$ a = Eval $ \ h k -> runEval f h (eval h k . ($ a))

  unit = pure ()

  inlr = liftA2 (,)
  exl = fmap fst
  exr = fmap snd

  inl = fmap Left
  inr = fmap Right
  exlr f g e = Eval $ \ h k -> runEval e h (eval h k . either (f . pure) (g . pure))

  true  = pure True
  false = pure False
  iff c t e = Eval $ \ h k -> runEval c h (eval h k . bool e t)

  alg (Eff s k) = Eval $ \ h k' -> handle s (eval h k' . k) (error "TBD")


newtype Handler (sig :: Type -> Type) r = Handler { runHandler :: forall a . sig a -> (a -> r) -> r }

handle :: sig a -> (a -> r) -> Handler sig r -> r
handle e k h = runHandler h e k
