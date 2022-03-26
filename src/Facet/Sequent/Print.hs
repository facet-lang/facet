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
  lamR c = P.braces (fresh (\ u -> fresh (\ v -> anon u <> P.comma P.<+> anon v P.<+> P.pretty "." P.<+> c (anon u) (anon v))))
  sumR1 t = P.parens (P.pretty "inl" P.<+> t)
  sumR2 t = P.parens (P.pretty "inr" P.<+> t)
  unitR = P.parens mempty
  prdR l r = P.tupled [l, r]
  stringR = P.pretty . show

  covar = var
  µL b = µ̃ <> P.braces (fresh (\ v -> anon v P.<+> P.dot P.<+> b (anon v)))
  lamL a k = a P.<+> P.dot P.<+> k
  sumL l r = P.pretty "case" <> P.braces (commaSep [l, r])
  unitL = P.pretty "_"
  prdL1 k = P.parens (µ̃ <> P.braces (P.pretty "πl" P.<+> k))
  prdL2 k = P.parens (µ̃ <> P.braces (P.pretty "πr" P.<+> k))

  (.|.) = fmap (P.enclose P.langle P.rangle) . P.surround P.pipe
  let' v b = P.pretty "let" P.<+> withLevel anon P.<+> P.pretty '=' P.<+> v P.<+> P.pretty "in" P.<+> fresh (b . anon)

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
