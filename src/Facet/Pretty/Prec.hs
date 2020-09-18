{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Pretty.Prec
( Level(..)
, PrecPrinter(..)
, infix'
, infixl'
, infixr'
, runPrec
, Prec(..)
, module Facet.Pretty) where

import Control.Applicative (liftA2)
import Facet.Pretty
import Facet.Pretty.Fresh
import Facet.Pretty.Rainbow

newtype Level = Level { getLevel :: Int }
  deriving (Bounded, Enum, Eq, Ord, Show)


class (Bounded lvl, Enum lvl, Ord lvl, Printer ann doc) => PrecPrinter lvl ann doc | doc -> ann lvl where
  prec :: lvl -> doc -> doc
  resetPrec :: lvl -> doc -> doc
  askingPrec :: (lvl -> doc) -> doc

infix' :: PrecPrinter lvl ann doc => lvl -> (doc -> doc -> doc) -> (doc -> doc -> doc)
infix' lv sep l r = prec lv (sep (prec (succ lv) l) (prec (succ lv) r))

infixl' :: PrecPrinter lvl ann doc => lvl -> (doc -> doc -> doc) -> (doc -> doc -> doc)
infixl' lv sep l r = prec lv (sep l (prec (succ lv) r))

infixr' :: PrecPrinter lvl ann doc => lvl -> (doc -> doc -> doc) -> (doc -> doc -> doc)
infixr' lv sep l r = prec lv (sep (prec (succ lv) l) r)


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

  nest = fmap . nest

  group = fmap group

  flatAlt = liftA2 flatAlt

  parens   = fmap parens   . resetPrec (Level 0)
  brackets = fmap brackets . resetPrec (Level 0)
  braces   = fmap braces   . resetPrec (Level 0)

instance Printer ann doc => PrecPrinter Level ann (Prec doc) where
  prec l (Prec d) = Prec $ \ l' -> parensIf (l' > l) (d l)
  resetPrec l (Prec d) = Prec $ \ _ -> d l
  askingPrec f = Prec $ runPrec <*> f

instance PrecPrinter lvl ann a => PrecPrinter lvl ann (b -> a) where
  prec = fmap . prec
  resetPrec = fmap . resetPrec
  askingPrec f b = askingPrec (($ b) . f)

deriving instance PrecPrinter lvl (Nest ann) doc => PrecPrinter lvl (Nest ann) (Rainbow doc)
deriving instance PrecPrinter lvl       ann  doc => PrecPrinter lvl       ann  (Fresh   doc)
