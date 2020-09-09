{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE KindSignatures #-}
module Facet.Eval
( Eval(..)
) where

import Data.Kind (Type)

newtype Eval (sig :: (Type -> Type) -> (Type -> Type)) a = Eval { eval :: a }
  deriving (Functor)
