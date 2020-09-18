{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
-- FIXME: virtualize nestRainbow
module Facet.Pretty.Rainbow
( Nesting(..)
, Nest(..)
, rainbow
, Rainbow(..)
, module Facet.Pretty
) where

import Control.Applicative (liftA2)
import Facet.Pretty

newtype Nesting = Nesting { getNesting :: Int }
  deriving (Eq, Ord, Show)

data Nest a
  = Nest Nesting
  | Ann a
  deriving (Eq, Ord, Show)

rainbow :: Rainbow doc -> doc
rainbow = (`runRainbow` Nesting 0)

newtype Rainbow doc = Rainbow { runRainbow :: Nesting -> doc }
  deriving (Applicative, Functor, Monad, Monoid, Semigroup)

instance Show doc => Show (Rainbow doc) where
  showsPrec p = showsPrec p . rainbow

instance Printer (Nest ann) doc => Printer (Nest ann) (Rainbow doc) where
  pretty = pure . pretty

  hardline = pure hardline

  annotate = fmap . annotate

  align = fmap align

  group = fmap group

  flatAlt = liftA2 flatAlt

  parens   = nestRainbow lparen   rparen
  brackets = nestRainbow lbracket rbracket
  braces   = nestRainbow lbrace   rbrace

nestRainbow :: Printer (Nest ann) doc => doc -> doc -> Rainbow doc -> Rainbow doc
nestRainbow l r (Rainbow run) = Rainbow $ \ lv -> annotate (Nest lv) l <> run (Nesting (1 + getNesting lv)) <> annotate (Nest lv) r
