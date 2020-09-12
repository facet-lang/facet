{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Eval
( Eval(..)
, Val(..)
, eval0
) where

import Control.Applicative (liftA, liftA2)
import Data.Bifunctor (bimap, first)
import Data.Functor.Identity
import Data.Kind (Type)
import Facet.Expr

newtype Eval (sig :: Type -> Type) a = Eval { eval :: forall r . (Either a (Eff sig (Eval sig a)) -> r) -> r }

newtype Val a = Val { getVal :: a }

eval0 :: Eval None a -> a
eval0 m = eval m (either id (\ (Eff e _) -> absurd e))

instance Functor (Eval sig) where
  fmap = liftA

instance Applicative (Eval sig) where
  pure a = Eval $ \ k -> k (Left a)

  f <*> a = Eval $ \ k -> eval f $ either
    (\ f' -> eval a (k . bimap f' (fmap (fmap f'))))
    (k . Right . fmap (<*> a))

instance Monad (Eval sig) where
  m >>= f = Eval $ \ k -> eval m $ either
    ((`eval` k) . f)
    (k . Right . fmap (>>= f))

instance Expr Identity Eval where
  val = pure . runIdentity

  -- k (Left …) indicates that we don’t need to perform effects to construct the lambda itself, even if it uses effects to do its job
  lam f = Eval $ \ k -> k (Left (`eval` f . first pure))
  f $$ a = Eval $ \ k -> eval f $ \case
    Left  f' -> eval (f' a) k
    Right f' -> eval (alg f' >>= \ f' -> f' a) k

  unit = pure ()

  inlr = liftA2 (,)
  exl = fmap fst
  exr = fmap snd

  inl = fmap Left
  inr = fmap Right
  exlr f g e = Eval $ \ k -> eval e $ \case
    Left  e -> eval (either (f . pure) (g . pure) e) k
    Right e -> k (Right (exlr f g <$> e))

  true  = pure True
  false = pure False
  iff c t e = Eval $ \ k -> eval c $ \case
    Left  c' -> eval (if c' then t else e) k
    Right c' -> k (Right (fmap (\ c -> iff c t e) c'))

  alg s = Eval $ \ k -> k (Right s)
