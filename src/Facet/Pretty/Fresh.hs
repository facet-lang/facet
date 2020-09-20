{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Facet.Pretty.Fresh
( FreshPrinter(..)
, fresh
, Fresh(..)
, module Facet.Pretty
) where

import Facet.Pretty

class Printer ann doc => FreshPrinter ann doc where
  bind :: (Int -> doc) -> doc

fresh :: Fresh doc -> doc
fresh = (`runFresh` 0)

newtype Fresh doc = Fresh { runFresh :: Int -> doc }
  deriving (Applicative, Printer ann, Functor, Monad, Monoid, Semigroup)

instance Show doc => Show (Fresh doc) where
  showsPrec p = showsPrec p . fresh

instance FreshPrinter ann a => FreshPrinter ann (b -> a) where
  bind f a = bind (($ a) . f)

instance (FreshPrinter ann a, FreshPrinter ann b) => FreshPrinter ann (a, b) where
  bind f = (bind (fst . f), bind (snd . f))

instance Printer ann doc => FreshPrinter ann (Fresh doc) where
  bind f = Fresh $ \ v -> runFresh (f v) (succ v)
