{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Sequent.Print
( Print(..)
) where

import           Facet.Name
import           Facet.Pretty
import           Facet.Print.Options
import qualified Facet.Sequent.Class as S
import qualified Facet.Style as S
import           Facet.Syntax
import qualified Prettyprinter as PP
import qualified Silkscreen as P
import qualified Silkscreen.Printer.Rainbow as P

newtype Print = Print { doc :: Options Print -> Used -> P.Rainbow (PP.Doc S.Style) }
  deriving (Monoid, P.Printer, Semigroup)

getPrint :: Options Print -> Print -> PP.Doc S.Style
getPrint o p = P.runRainbow (P.annotate . S.Nest) 0 (doc (P.group p) o 0)

instance Show Print where
  showsPrec p = showsPrec p . getPrint quietOptions


instance S.Sequent Print Print Print where
  var = var
  µR b = P.pretty "µ" <> P.braces (fresh (\ v -> anon v P.<+> P.dot P.<+> b (anon v)))
  lamR c = P.braces (fresh (\ u -> fresh (\ v -> P.brackets (anon u <> P.comma P.<+> anon v) P.<+> P.pretty "->" P.<+> c (anon u) (anon v))))
  sumR i t = P.parens (P.pretty "in" <> P.pretty i P.<+> t)
  prdR = P.tupled
  stringR = P.pretty . show

  covar = var
  µL b = µ̃ <> P.braces (fresh (\ v -> anon v P.<+> P.dot P.<+> b (anon v)))
  lamL a k = a P.<+> P.dot P.<+> k
  sumL cs = µ̃ <> P.braces (commaSep (map (\ c -> fresh (\ v -> anon v P.<+> P.dot P.<+> c (anon v))) cs))
  prdL i k = P.parens (µ̃ <> withLevel (\ d -> k (map (\ i -> anon (d + fromIntegral i)) [0..i])))

  (.|.) = fmap (P.enclose P.langle P.rangle) . P.surround P.pipe

withLevel :: (Used -> Print) -> Print
withLevel f = Print (\ o d -> doc (f d) o d)

incrLevel :: Print -> Print
incrLevel p = Print (\ o -> doc p o . succ)

fresh :: (Used -> Print) -> Print
fresh f = withLevel (incrLevel . f)

anon :: Used -> Print
anon = lower . getLevel . getUsed

var :: Var Level -> Print
var v = case v of
  Free l   -> lower (getLevel l)
  Global n -> P.pretty n

commaSep :: [Print] -> Print
commaSep = P.encloseSep mempty mempty (P.comma <> P.space)

µ̃ :: Print
µ̃ = P.pretty "µ̃"
