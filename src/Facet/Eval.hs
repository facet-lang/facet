{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE KindSignatures #-}
module Facet.Eval
( Eval(..)
) where

import Data.Functor.Identity
import Data.Kind (Type)
import Facet.Expr

newtype Eval (sig :: Bin ((Type -> Type) -> (Type -> Type))) a = Eval { eval :: a }
  deriving (Applicative, Functor) via Identity
