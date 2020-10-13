module Facet.Print.Applicative
( pretty
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
