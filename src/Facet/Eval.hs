{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Eval
( Eval(..)
) where

import Data.Kind (Type)
import Facet.Expr

newtype Eval (sig :: Bin (Type -> Type)) a = Eval { eval :: forall r . (a -> r) -> r }
  deriving (Functor)

instance Applicative (Eval sig) where
  pure a = Eval $ \ k -> k a

  Eval f <*> Eval a = Eval $ \ k -> f $ \ f' -> a $ \ a' -> k (f' a')

instance Monad (Eval sig) where
  m >>= f = Eval $ \ k -> eval m $ \ a -> eval (f a) k
