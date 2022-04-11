module Facet.Functor.Check
( -- * Check judgement
  type (<==:)(..)
, (<==:)
) where

import Data.Profunctor

-- Check judgement

newtype b <==: a = Check { runCheck :: b -> a }
  deriving (Applicative, Functor, Monad, Profunctor)

infixl 2 <==:

(<==:) :: b <==: a -> b -> a
Check f <==: _T = f _T
