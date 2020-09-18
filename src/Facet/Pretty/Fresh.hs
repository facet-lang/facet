{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Pretty.Fresh
( Var(..)
, FreshPrinter(..)
, fresh
, Fresh(..)
, module Facet.Pretty
) where

import Facet.Pretty

newtype Var = Var { getVar :: Int }
  deriving (Eq, Ord, Show)

incr :: Var -> Var
incr = Var . succ . getVar


class Printer ann doc => FreshPrinter ann doc where
  bind :: (Var -> doc) -> doc

fresh :: Fresh doc -> doc
fresh = (`runFresh` Var 0)

newtype Fresh doc = Fresh { runFresh :: Var -> doc }
  deriving (Applicative, Printer ann, Functor, Monad, Monoid, Semigroup)

instance Show doc => Show (Fresh doc) where
  showsPrec p = showsPrec p . fresh

instance FreshPrinter ann a => FreshPrinter ann (b -> a) where
  bind f a = bind (($ a) . f)

instance Printer ann doc => FreshPrinter ann (Fresh doc) where
  bind f = Fresh $ \ v -> runFresh (f v) (incr v)
