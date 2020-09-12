{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
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
import Control.Monad ((<=<))
import Data.Bifunctor (bimap, first)
import Data.Kind (Type)
import Facet.Expr

newtype Eval (sig :: Type -> Type) a = Eval { runEval :: () -> forall r . (Either a (Eff sig (Eval sig a)) -> r) -> r }

eval :: () -> (Either a (Eff sig (Eval sig a)) -> r) -> Eval sig a -> r
eval h k e = runEval e h k

eval0 :: Eval None a -> a
eval0 = eval () (either id (\ (Eff e _) -> absurd e))

instance Functor (Eval sig) where
  fmap = liftA

instance Applicative (Eval sig) where
  pure a = Eval $ \ _ k -> k (Left a)

  f <*> a = Eval $ \ h k -> runEval f h $ either
    (\ f' -> runEval a h (k . bimap f' (fmap (fmap f'))))
    (k . Right . fmap (<*> a))

instance Monad (Eval sig) where
  m >>= f = Eval $ \ h k -> runEval m h $ either
    (eval h k . f)
    (k . Right . fmap (>>= f))

instance Expr Eval where
  val = pure . eval0

  -- k (Left …) indicates that we don’t need to perform effects to construct the lambda itself, even if it uses effects to do its job
  lam f = Eval $ \ h k -> k (Left (eval h (f . first pure)))
  f $$ a = Eval $ \ h k -> runEval f h $ eval h k . either ($ a) (($ a) <=< alg)

  unit = pure ()

  inlr = liftA2 (,)
  exl = fmap fst
  exr = fmap snd

  inl = fmap Left
  inr = fmap Right
  exlr f g e = Eval $ \ h k -> runEval e h $ \case
    Left  e -> runEval (either (f . pure) (g . pure) e) h k
    Right e -> k (Right (exlr f g <$> e))

  true  = pure True
  false = pure False
  iff c t e = Eval $ \ h k -> runEval c h $ \case
    Left  c' -> runEval (if c' then t else e) h k
    Right c' -> k (Right (fmap (\ c -> iff c t e) c'))

  alg s = Eval $ \ _ k -> k (Right s)


newtype Handler (sig :: Type -> Type) = Handler { runHandler :: forall a k . Eff sig a -> (a -> k) -> k }

handle :: Eff sig a -> (a -> k) -> Handler sig -> k
handle e k h = runHandler h e k
