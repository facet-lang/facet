{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
-- FIXME: move this whole module into a new package?
module Facet.Pretty
( hPutDoc
, putDoc
, PP.Pretty
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
) where

import           Control.Applicative (liftA2)
import           Control.Monad.IO.Class
import           Data.Monoid (Ap(..))
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import           System.Console.Terminal.Size as Size
import           System.IO (Handle, stdout)

hPutDoc :: MonadIO m => Handle -> PP.Doc ANSI.AnsiStyle -> m ()
hPutDoc handle doc = do
  s <- maybe 80 Size.width <$> liftIO size
  liftIO (ANSI.renderIO handle (PP.layoutSmart PP.defaultLayoutOptions { PP.layoutPageWidth = PP.AvailablePerLine s 0.8 } (doc <> PP.line)))

putDoc :: MonadIO m => PP.Doc ANSI.AnsiStyle -> m ()
putDoc = hPutDoc stdout


class Monoid doc => Printer ann doc | doc -> ann where
  pretty :: PP.Pretty a => a -> doc

  hardline :: doc

  annotate :: ann -> doc -> doc

  align :: doc -> doc

  nest :: Int -> doc -> doc

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

  nest = PP.nest

  group = PP.group

  flatAlt = PP.flatAlt

instance (Applicative f, Printer ann a) => Printer ann (Ap f a) where
  pretty = pure . pretty

  hardline = pure hardline

  annotate = fmap . annotate

  align = fmap align

  nest = fmap . nest

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

  nest = fmap . nest

  group = fmap group

  flatAlt = liftA2 flatAlt

  parens = fmap parens

  brackets = fmap brackets

  braces = fmap braces

instance (Printer ann a, Printer ann b) => Printer ann (a, b) where
  pretty a = (pretty a, pretty a)

  hardline = (hardline, hardline)

  annotate ann (a, b) = (annotate ann a, annotate ann b)

  align (a, b) = (align a, align b)

  nest i (a, b) = (nest i a, nest i b)

  group (a, b) = (group a, group b)

  flatAlt (a1, a2) (b1, b2) = (flatAlt a1 b1, flatAlt a2 b2)

  parens (a, b) = (parens a, parens b)

  brackets (a, b) = (brackets a, brackets b)

  braces (a, b) = (braces a, braces b)

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
