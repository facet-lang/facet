{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE KindSignatures #-}
module Facet.Eval
( Eval(..)
) where

import Data.Functor.Identity
import Data.Kind (Type)

newtype Eval (sig :: (Type -> Type) -> (Type -> Type)) a = Eval { eval :: a }
  deriving (Applicative, Functor) via Identity
