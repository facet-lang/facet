{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Pretty
( putDoc
, Doc(..)
, space
, line
, line'
, lparen
, rparen
, lbracket
, rbracket
, lbrace
, rbrace
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
, PrecDoc(..)
, runPrec
, Prec(..)
, Nesting(..)
, rainbow
, Rainbow(..)
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


class Monoid doc => Doc ann doc | doc -> ann where
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

instance Doc ann (PP.Doc ann) where
  pretty = PP.pretty

  hardline = PP.hardline

  annotate = PP.annotate

  align = PP.align

  group = PP.group

  flatAlt = PP.flatAlt

instance (Applicative f, Doc ann a) => Doc ann (Ap f a) where
  pretty = pure . pretty

  hardline = pure hardline

  annotate = fmap . annotate

  align = fmap align

  group = fmap group

  flatAlt = liftA2 flatAlt

  parens = fmap parens

  brackets = fmap brackets

  braces = fmap braces

space :: Doc ann doc => doc
space = pretty ' '

line :: Doc ann doc => doc
line = flatAlt hardline space

line' :: Doc ann doc => doc
line' = flatAlt hardline mempty

lparen, rparen :: Doc ann doc => doc
lparen = pretty "("
rparen = pretty ")"

lbracket, rbracket :: Doc ann doc => doc
lbracket = pretty "["
rbracket = pretty "]"

lbrace, rbrace :: Doc ann doc => doc
lbrace = pretty "{"
rbrace = pretty "}"

enclose :: Doc ann doc => doc -> doc -> doc -> doc
enclose l r x = l <> x <> r

surround :: Doc ann doc => doc -> doc -> doc -> doc
surround x l r = enclose l r x

encloseSep :: Doc ann doc => doc -> doc -> doc -> [doc] -> doc
encloseSep l r s ds = case ds of
  []  -> l <> r
  [d] -> l <> d <> r
  _   -> cat (zipWith (<>) (l : repeat s) ds) <> r

tupled :: Doc ann doc => [doc] -> doc
tupled
  = group
  . encloseSep
    (lparen <> flatAlt space mempty)
    (flatAlt space mempty <> rparen)
    (pretty ", ")

cat :: Doc ann doc => [doc] -> doc
cat = group . vcat

vcat :: Doc ann doc => [doc] -> doc
vcat = concatWith (surround line')

sep :: Doc ann doc => [doc] -> doc
sep = group . vsep

vsep :: Doc ann doc => [doc] -> doc
vsep = concatWith (</>)

concatWith :: (Doc ann doc, Foldable t) => (doc -> doc -> doc) -> t doc -> doc
concatWith (<>) ds
  | null ds   = mempty
  | otherwise = foldr1 (<>) ds

(<+>) :: Doc ann doc => doc -> doc -> doc
(<+>) = surround space

infixr 6 <+>

(</>) :: Doc ann doc => doc -> doc -> doc
(</>) = surround line

infixr 6 </>

parensIf :: Doc ann doc => Bool -> doc -> doc
parensIf True = parens
parensIf _    = id


newtype Level = Level Int
  deriving (Eq, Ord, Show)

class Doc ann doc => PrecDoc ann doc where
  prec :: Level -> doc -> doc
  resetPrec :: Level -> doc -> doc


runPrec :: Level -> Prec a -> a
runPrec l (Prec run) = run l

newtype Prec a = Prec (Level -> a)
  deriving (Applicative, Functor, Monad, Monoid, Semigroup)

instance Show a => Show (Prec a) where
  showsPrec p = showsPrec p . runPrec (Level p)

instance Doc ann doc => Doc ann (Prec doc) where
  pretty = pure . pretty

  hardline = pure hardline

  annotate = fmap . annotate

  align = fmap align

  group = fmap group

  flatAlt = liftA2 flatAlt

  parens   = fmap parens   . resetPrec (Level 0)
  brackets = fmap brackets . resetPrec (Level 0)
  braces   = fmap braces   . resetPrec (Level 0)

instance Doc ann doc => PrecDoc ann (Prec doc) where
  prec l (Prec d) = Prec $ \ l' -> parensIf (l' > l) (d l)
  resetPrec l (Prec d) = Prec $ \ _ -> d l

instance (Applicative f, PrecDoc ann a) => PrecDoc ann (Ap f a) where
  prec = fmap . prec
  resetPrec = fmap . resetPrec


newtype Nesting = Nesting { getNesting :: Int }
  deriving (Eq, Ord, Show)

rainbow :: Rainbow doc -> doc
rainbow = (`runRainbow` Nesting 0)

newtype Rainbow doc = Rainbow { runRainbow :: Nesting -> doc }
  deriving (Applicative, Functor, Monad, Monoid, Semigroup)

instance Show doc => Show (Rainbow doc) where
  showsPrec p = showsPrec p . rainbow

instance (Doc (ann Nesting) doc, Applicative ann) => Doc (ann Nesting) (Rainbow doc) where
  pretty = pure . pretty

  hardline = pure hardline

  annotate = fmap . annotate

  align = fmap align

  group = fmap group

  flatAlt = liftA2 flatAlt

  parens   = nestRainbow (pretty '(') (pretty ')')
  brackets = nestRainbow (pretty '[') (pretty ']')
  braces   = nestRainbow (pretty '{') (pretty '}')

nestRainbow :: (Doc (ann Nesting) doc, Applicative ann) => doc -> doc -> Rainbow doc -> Rainbow doc
nestRainbow l r (Rainbow run) = Rainbow $ \ lv -> annotate (pure lv) l <> run (Nesting (1 + getNesting lv)) <> annotate (pure lv) r

instance (PrecDoc (ann Nesting) doc, Applicative ann) => PrecDoc (ann Nesting) (Rainbow doc) where
  prec = fmap . prec
  resetPrec = fmap . resetPrec
