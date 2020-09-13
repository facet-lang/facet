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
import Control.Monad (ap)
import Control.Monad.Trans.Cont
import Control.Monad.Trans.Reader
import Data.Bool (bool)
import Data.Kind (Type)
import Facet.Expr

newtype Eval (sig :: Type -> Type) a = Eval { runEval :: forall r . ReaderT (Handler None r) (Cont r) a }

eval :: Handler None r -> (a -> r) -> Eval sig a -> r
eval h k e = runCont (runReaderT (runEval e) h) k

eval0 :: Eval None a -> a
eval0 = eval (Handler (const . absurd)) id

instance Functor (Eval sig) where
  fmap = liftA

instance Applicative (Eval sig) where
  pure a = Eval $ pure a

  (<*>) = ap

instance Monad (Eval sig) where
  m >>= f = Eval $ runEval m >>= runEval . f

instance Expr Eval where
  val = pure . eval0

  lam f = Eval $ pure $ f . Left . eval (Handler (const . absurd)) pure
  f $$ a = Eval $ runEval f >>= runEval . ($ a)

  unit = pure ()

  inlr = liftA2 (,)
  exl = fmap fst
  exr = fmap snd

  inl = fmap Left
  inr = fmap Right
  exlr f g e = e >>= either (f . pure) (g . pure)

  true  = pure True
  false = pure False
  iff c t e = Eval $ runEval c >>= runEval . bool e t

  alg (Eff s k) = Eval $ handle s (runEval . k) (error "TBD")


newtype Handler (sig :: Type -> Type) r = Handler { runHandler :: forall a . sig a -> (a -> r) -> r }

handle :: sig a -> (a -> r) -> Handler sig r -> r
handle e k h = runHandler h e k
