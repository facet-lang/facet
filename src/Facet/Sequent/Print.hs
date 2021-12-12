{-# LANGUAGE UndecidableInstances #-}
module Facet.Sequent.Print
( Print(..)
) where

import qualified Facet.Style as S
import qualified Prettyprinter as PP
import qualified Silkscreen as P
import qualified Silkscreen.Printer.Rainbow as P

newtype Print = Print { doc :: P.Rainbow (PP.Doc S.Style) }
  deriving (Monoid, P.Printer, Semigroup)
