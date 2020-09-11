{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Eval
( Eval(..)
) where

import Control.Applicative (liftA)
import Data.Bifunctor (bimap)
import Data.Kind (Type)
import Facet.Expr

newtype Eval (sig :: Bin (Type -> Type)) a = Eval { eval :: forall r . (Either a (Sig sig (Eval sig a)) -> r) -> r }

instance Functor (Eval sig) where
  fmap = liftA

instance Applicative (Eval sig) where
  pure a = Eval $ \ k -> k (Left a)

  f <*> a = Eval $ \ k -> eval f $ either
    (\ f' -> eval a $ \ a' -> k (bimap f' (fmap (fmap f')) a'))
    (k . Right . fmap (<*> a))

instance Monad (Eval sig) where
  m >>= f = Eval $ \ k -> eval m $ either
    (\ a -> eval (f a) k)
    (k . Right . fmap (>>= f))
