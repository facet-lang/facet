{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Pretty.Prec
( Level(..)
, PrecPrinter(..)
, prec
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


class Printer ann doc => PrecPrinter lvl ann doc | doc -> ann lvl where
  askingPrec :: (lvl -> doc) -> doc
  localPrec :: (lvl -> lvl) -> doc -> doc

prec :: (PrecPrinter lvl ann doc, Ord lvl) => lvl -> doc -> doc
prec l d = askingPrec $ \ l' -> parensIf (l' > l) (localPrec (const l) d)

infix' :: (PrecPrinter lvl ann doc, Ord lvl) => lvl -> lvl -> (doc -> doc -> doc) -> (doc -> doc -> doc)
infix' lo hi sep l r = prec lo (sep (prec hi l) (prec hi r))

infixl' :: (PrecPrinter lvl ann doc, Ord lvl) => lvl -> lvl -> (doc -> doc -> doc) -> (doc -> doc -> doc)
infixl' lo hi sep l r = prec lo (sep l (prec hi r))

infixr' :: (PrecPrinter lvl ann doc, Ord lvl) => lvl -> lvl -> (doc -> doc -> doc) -> (doc -> doc -> doc)
infixr' lo hi sep l r = prec lo (sep (prec hi l) r)


runPrec :: lvl -> Prec lvl a -> a
runPrec l (Prec run) = run l

newtype Prec lvl a = Prec (lvl -> a)
  deriving (Applicative, Functor, Monad, Monoid, Semigroup)

instance (Bounded lvl, Show a) => Show (Prec lvl a) where
  showsPrec p = showsPrec p . runPrec minBound

instance (Bounded lvl, Printer ann doc) => Printer ann (Prec lvl doc) where
  pretty = pure . pretty

  hardline = pure hardline

  annotate = fmap . annotate

  align = fmap align

  nest = fmap . nest

  group = fmap group

  flatAlt = liftA2 flatAlt

  parens   = fmap parens   . localPrec (const minBound)
  brackets = fmap brackets . localPrec (const minBound)
  braces   = fmap braces   . localPrec (const minBound)

instance (Bounded lvl, Printer ann doc) => PrecPrinter lvl ann (Prec lvl doc) where
  askingPrec f = Prec $ runPrec <*> f
  localPrec l (Prec d) = Prec $ d . l

instance PrecPrinter lvl ann a => PrecPrinter lvl ann (b -> a) where
  askingPrec f b = askingPrec (($ b) . f)
  localPrec = fmap . localPrec

deriving instance PrecPrinter lvl (Nest ann) doc => PrecPrinter lvl (Nest ann) (Rainbow doc)
deriving instance PrecPrinter lvl       ann  doc => PrecPrinter lvl       ann  (Fresh   doc)
