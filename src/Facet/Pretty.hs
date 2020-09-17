{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
-- FIXME: move this whole module into a new package?
module Facet.Pretty
( putDoc
, Printer(..)
, space
, line
, line'
, lparen
, rparen
, lbracket
, rbracket
, lbrace
, rbrace
, comma
, colon
, enclose
, surround
, encloseSep
, tupled
, cat
, vcat
, sep
, vsep
, concatWith
, (<+>)
, (</>)
, parensIf
, Level(..)
, PrecPrinter(..)
, runPrec
, Prec(..)
, Nesting(..)
, Nest(..)
, rainbow
, Rainbow(..)
, Var(..)
, fresh
, bind
, Fresh(..)
) where

import           Control.Applicative (liftA2)
import           Control.Monad.IO.Class
import           Data.Monoid (Ap(..))
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Text.Prettyprint.Doc.Render.Terminal as ANSI
import           System.Console.Terminal.Size as Size
import           System.IO (stdout)

putDoc :: MonadIO m => PP.Doc ANSI.AnsiStyle -> m ()
putDoc doc = do
  s <- maybe 80 Size.width <$> liftIO size
  liftIO (ANSI.renderIO stdout (PP.layoutSmart PP.defaultLayoutOptions { PP.layoutPageWidth = PP.AvailablePerLine s 0.8 } (doc <> PP.line)))


class Monoid doc => Printer ann doc | doc -> ann where
  pretty :: PP.Pretty a => a -> doc

  hardline :: doc

  annotate :: ann -> doc -> doc

  align :: doc -> doc

  group :: doc -> doc

  flatAlt :: doc -> doc -> doc

  parens :: doc -> doc
  parens = enclose lparen rparen

  brackets :: doc -> doc
  brackets = enclose lbracket rbracket

  braces :: doc -> doc
  braces = enclose lbrace rbrace

instance Printer ann (PP.Doc ann) where
  pretty = PP.pretty

  hardline = PP.hardline

  annotate = PP.annotate

  align = PP.align

  group = PP.group

  flatAlt = PP.flatAlt

instance (Applicative f, Printer ann a) => Printer ann (Ap f a) where
  pretty = pure . pretty

  hardline = pure hardline

  annotate = fmap . annotate

  align = fmap align

  group = fmap group

  flatAlt = liftA2 flatAlt

  parens = fmap parens

  brackets = fmap brackets

  braces = fmap braces

instance Printer ann a => Printer ann (b -> a) where
  pretty = pure . pretty

  hardline = pure hardline

  annotate = fmap . annotate

  align = fmap align

  group = fmap group

  flatAlt = liftA2 flatAlt

  parens = fmap parens

  brackets = fmap brackets

  braces = fmap braces

space :: Printer ann doc => doc
space = pretty ' '

line :: Printer ann doc => doc
line = flatAlt hardline space

line' :: Printer ann doc => doc
line' = flatAlt hardline mempty

lparen, rparen :: Printer ann doc => doc
lparen = pretty '('
rparen = pretty ')'

lbracket, rbracket :: Printer ann doc => doc
lbracket = pretty '['
rbracket = pretty ']'

lbrace, rbrace :: Printer ann doc => doc
lbrace = pretty '{'
rbrace = pretty '}'

comma :: Printer ann doc => doc
comma = pretty ','

colon :: Printer ann doc => doc
colon = pretty ':'

enclose :: Printer ann doc => doc -> doc -> doc -> doc
enclose l r x = l <> x <> r

surround :: Printer ann doc => doc -> doc -> doc -> doc
surround x l r = enclose l r x

encloseSep :: Printer ann doc => doc -> doc -> doc -> [doc] -> doc
encloseSep l r s ds = case ds of
  []  -> l <> r
  [d] -> l <> d <> r
  _   -> cat (zipWith (<>) (l : repeat s) ds) <> r

tupled :: Printer ann doc => [doc] -> doc
tupled
  = group
  . encloseSep
    (lparen <> flatAlt space mempty)
    (flatAlt space mempty <> rparen)
    (pretty ", ")

cat :: Printer ann doc => [doc] -> doc
cat = group . vcat

vcat :: Printer ann doc => [doc] -> doc
vcat = concatWith (surround line')

sep :: Printer ann doc => [doc] -> doc
sep = group . vsep

vsep :: Printer ann doc => [doc] -> doc
vsep = concatWith (</>)

concatWith :: (Printer ann doc, Foldable t) => (doc -> doc -> doc) -> t doc -> doc
concatWith (<>) ds
  | null ds   = mempty
  | otherwise = foldr1 (<>) ds

(<+>) :: Printer ann doc => doc -> doc -> doc
(<+>) = surround space

infixr 6 <+>

(</>) :: Printer ann doc => doc -> doc -> doc
(</>) = surround line

infixr 6 </>

parensIf :: Printer ann doc => Bool -> doc -> doc
parensIf True = parens
parensIf _    = id


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

instance PrecPrinter (Nest ann) doc => PrecPrinter (Nest ann) (Rainbow doc) where
  prec = fmap . prec
  resetPrec = fmap . resetPrec


newtype Var = Var { getVar :: Int }
  deriving (Eq, Ord, Show)

instance PP.Pretty Var where
  pretty = pretty . getVar

incr :: Var -> Var
incr = Var . succ . getVar


fresh :: Fresh doc -> doc
fresh = (`runFresh` Var 0)

bind :: (Var -> Fresh doc) -> Fresh doc
bind f = Fresh $ \ v -> runFresh (f v) (incr v)

newtype Fresh doc = Fresh { runFresh :: Var -> doc }
  deriving (Applicative, Printer ann, Functor, Monad, Monoid, PrecPrinter ann, Semigroup)

instance Show doc => Show (Fresh doc) where
  showsPrec p = showsPrec p . fresh
