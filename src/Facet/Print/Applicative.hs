module Facet.Print.Applicative
( pretty
, group
, flatAlt
, align
, hang
, indent
, nest
, concatWith
, hsep
, vsep
, fillSep
, sep
, hcat
, vcat
, fillCat
, cat
, punctuate
, (<:>)
, enclose
, surround
, (<+>)
, (</>)
, space
, line
, line'
, softline
, softline'
, hardline
) where

import           Control.Applicative (liftA2)
import           Silkscreen (Printer)
import qualified Silkscreen as S

pretty :: (Applicative f, Printer p, S.Pretty a) => a -> f p
pretty = pure . S.pretty


-- | Try to unwrap the argument, if it will fit.
group :: (Applicative f, Printer p) => f p -> f p
group = fmap S.group

-- | Print the first argument by default, or the second when an enclosing 'group' flattens it.
flatAlt :: (Applicative f, Printer p) => f p -> f p -> f p
flatAlt = liftA2 S.flatAlt


-- | Indent lines in the argument to the current column.
align :: (Applicative f, Printer p) => f p -> f p
align = fmap S.align

-- | Indent following lines in the argument to the current column + some delta.
hang :: (Applicative f, Printer p) => Int -> f p -> f p
hang = fmap . S.hang

-- | Indent lines in the argument to the current column + some delta.
indent :: (Applicative f, Printer p) => Int -> f p -> f p
indent = fmap . S.indent


-- | @'nest' i p@ changes the indentation level for new lines in @p@ by @i@.
nest :: (Applicative f, Printer p) => Int -> f p -> f p
nest = fmap . S.nest


concatWith :: (Applicative f, Monoid p, Foldable t) => (f p -> f p -> f p) -> t (f p) -> f p
concatWith (<>) ds
  | null ds   = pure mempty
  | otherwise = foldr1 (<>) ds


hsep :: (Applicative f, Printer p) => [f p] -> f p
hsep = concatWith (<+>)

vsep :: (Applicative f, Printer p) => [f p] -> f p
vsep = concatWith (</>)

fillSep :: (Applicative f, Printer p) => [f p] -> f p
fillSep = concatWith (surround softline)

sep :: (Applicative f, Printer p) => [f p] -> f p
sep = group . vsep


hcat :: (Applicative f, Printer p) => [f p] -> f p
hcat = fmap mconcat . sequenceA

vcat :: (Applicative f, Printer p) => [f p] -> f p
vcat = concatWith (surround line')

fillCat :: (Applicative f, Printer p) => [f p] -> f p
fillCat = concatWith (surround softline')

cat :: (Applicative f, Printer p) => [f p] -> f p
cat = group . vcat


punctuate :: (Applicative f, Printer p) => f p -> [f p] -> [f p]
punctuate s = go
  where
  go []     = []
  go [x]    = [x]
  go (x:xs) = liftA2 (<>) x s : go xs


(<:>) :: (Applicative f, Semigroup s) => f s -> f s -> f s
(<:>) = liftA2 (<>)

enclose :: (Applicative f, Printer p) => f p -> f p -> f p -> f p
enclose l r x = l <> x <> r
  where
  (<>) = liftA2 (Prelude.<>)


surround :: (Applicative f, Printer p) => f p -> f p -> f p -> f p
surround x l r = enclose l r x

(<+>) :: (Applicative f, Printer p) => f p -> f p -> f p
(<+>) = surround space

infixr 6 <+>

-- | Separate the arguments with a line.
(</>) :: (Applicative f, Printer p) => f p -> f p -> f p
(</>) = surround line

infixr 6 </>


space :: (Applicative f, Printer p) => f p
space = pure S.space

line :: (Applicative f, Printer p) => f p
line = pure S.line

line' :: (Applicative f, Printer p) => f p
line' = pure S.line'

softline :: (Applicative f, Printer p) => f p
softline = pure S.softline

softline' :: (Applicative f, Printer p) => f p
softline' = pure S.softline'

hardline :: (Applicative f, Printer p) => f p
hardline = pure S.hardline
