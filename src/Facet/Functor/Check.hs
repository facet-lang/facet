module Facet.Functor.Check
( -- * Check judgement
  type (<==:)(..)
, (<==:)
) where

-- Check judgement

newtype b <==: a = Check (b -> a)
  deriving (Applicative, Functor, Monad)

(<==:) :: b <==: a -> b -> a
Check f <==: _T = f _T

infixl 2 <==:
