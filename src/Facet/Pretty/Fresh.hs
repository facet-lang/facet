{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Pretty.Fresh
( Var(..)
, fresh
, bind
, Fresh(..)
, module Facet.Pretty
) where

import Facet.Pretty

newtype Var = Var { getVar :: Int }
  deriving (Eq, Ord, Show)

incr :: Var -> Var
incr = Var . succ . getVar


fresh :: Fresh doc -> doc
fresh = (`runFresh` Var 0)

bind :: (Var -> Fresh doc) -> Fresh doc
bind f = Fresh $ \ v -> runFresh (f v) (incr v)

newtype Fresh doc = Fresh { runFresh :: Var -> doc }
  deriving (Applicative, Printer ann, Functor, Monad, Monoid, Semigroup)

instance Show doc => Show (Fresh doc) where
  showsPrec p = showsPrec p . fresh
