{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE KindSignatures #-}
module Facet.Eval
( Eval(..)
) where

import Data.Kind (Type)
import Facet.Expr

newtype Eval r (sig :: Bin ((Type -> Type) -> (Type -> Type))) a = Eval { eval :: (a -> r) -> r }
  deriving (Functor)

instance Applicative (Eval r sig) where
  pure a = Eval $ \ k -> k a

  Eval f <*> Eval a = Eval $ \ k -> f $ \ f' -> a $ \ a' -> k (f' a')
