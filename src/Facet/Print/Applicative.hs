module Facet.Print.Applicative
( space
, (<+>)
) where

import           Control.Applicative (liftA2)
import           Silkscreen (Printer)
import qualified Silkscreen as S

space :: (Applicative f, Printer p) => f p
space = pure S.space


(<+>) :: (Applicative f, Printer p) => f p -> f p -> f p
a <+> b = liftA2 (\ a b -> a <> S.space <> b) a b
