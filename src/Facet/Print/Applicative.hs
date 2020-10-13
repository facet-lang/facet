module Facet.Print.Applicative
( pretty
, space
, (<+>)
) where

import           Control.Applicative (liftA2)
import           Silkscreen (Printer)
import qualified Silkscreen as S

pretty :: (Applicative f, Printer p, S.Pretty a) => a -> f p
pretty = pure . S.pretty

space :: (Applicative f, Printer p) => f p
space = pure S.space


(<+>) :: (Applicative f, Printer p) => f p -> f p -> f p
a <+> b = liftA2 (\ a b -> a <> S.space <> b) a b
