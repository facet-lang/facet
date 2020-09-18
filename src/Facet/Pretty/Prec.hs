{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Pretty.Prec
( Level(..)
, PrecPrinter(..)
, runPrec
, Prec(..)
, module Facet.Pretty) where

import Control.Applicative (liftA2)
import Data.Monoid (Ap(..))
import Facet.Pretty
import Facet.Pretty.Fresh
import Facet.Pretty.Rainbow

newtype Level = Level Int
  deriving (Eq, Ord, Show)

class Printer ann doc => PrecPrinter ann doc where
  prec :: Level -> doc -> doc
  resetPrec :: Level -> doc -> doc


runPrec :: Level -> Prec a -> a
runPrec l (Prec run) = run l

newtype Prec a = Prec (Level -> a)
  deriving (Applicative, Functor, Monad, Monoid, Semigroup)

instance Show a => Show (Prec a) where
  showsPrec p = showsPrec p . runPrec (Level p)

instance Printer ann doc => Printer ann (Prec doc) where
  pretty = pure . pretty

  hardline = pure hardline

  annotate = fmap . annotate

  align = fmap align

  group = fmap group

  flatAlt = liftA2 flatAlt

  parens   = fmap parens   . resetPrec (Level 0)
  brackets = fmap brackets . resetPrec (Level 0)
  braces   = fmap braces   . resetPrec (Level 0)

instance Printer ann doc => PrecPrinter ann (Prec doc) where
  prec l (Prec d) = Prec $ \ l' -> parensIf (l' > l) (d l)
  resetPrec l (Prec d) = Prec $ \ _ -> d l

instance (Applicative f, PrecPrinter ann a) => PrecPrinter ann (Ap f a) where
  prec = fmap . prec
  resetPrec = fmap . resetPrec

instance PrecPrinter ann a => PrecPrinter ann (b -> a) where
  prec = fmap . prec
  resetPrec = fmap . resetPrec

instance PrecPrinter (Nest ann) doc => PrecPrinter (Nest ann) (Rainbow doc) where
  prec = fmap . prec
  resetPrec = fmap . resetPrec

deriving instance PrecPrinter ann doc => PrecPrinter ann (Fresh doc)
