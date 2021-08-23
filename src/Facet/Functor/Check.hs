module Facet.Functor.Check
( -- * Check judgement
  Check(..)
, (<==:)
) where

import Facet.Type.Norm

-- Check judgement

newtype Check a = Check (Type -> a)
  deriving (Applicative, Functor, Monad)

(<==:) :: Check a -> Type -> a
Check f <==: _T = f _T

infixl 2 <==:
