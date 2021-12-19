{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Sequent.Print
( Print(..)
) where

import           Facet.Name
import           Facet.Pattern (Pattern(..))
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
  funR cs = P.braces (P.encloseSep (P.flatAlt P.space mempty) (P.flatAlt P.space mempty) (P.comma <> P.space) (map (uncurry clause) cs))
  sumR i t = P.parens (P.pretty "in" <> P.pretty i P.<+> t)
  prdR = P.tupled
  conR n fs = foldl1 (P.surround P.space) (S.var (Global n):fs)
  stringR = P.pretty . show
  dictR os = withOpts (\ Options{..} -> P.brackets (P.flatAlt P.space P.line <> commaSep (map (\ (n :=: v) -> rname n P.<+> P.equals P.<+> P.group v) os) <> P.flatAlt P.space P.line))
  compR p b = P.group
    . P.align
    . P.braces
    . P.enclose P.space P.space $ clause (PDict p) b

  covar = var
  µL b = µ̃ <> P.braces (fresh (\ v -> anon v P.<+> P.dot P.<+> b (anon v)))
  funL a k = a P.<+> P.dot P.<+> k
  sumL cs = µ̃ <> P.braces (commaSep (map (\ c -> fresh (\ v -> anon v P.<+> P.dot P.<+> c (anon v))) cs))

  (.|.) = fmap (P.enclose P.langle P.rangle) . P.surround P.pipe

withLevel :: (Used -> Print) -> Print
withLevel f = Print (\ o d -> doc (f d) o d)

incrLevel :: Print -> Print
incrLevel p = Print (\ o -> doc p o . succ)

fresh :: (Used -> Print) -> Print
fresh f = withLevel (incrLevel . f)

anon :: Used -> Print
anon = lower . getLevel . getUsed

withOpts :: (Options Print -> Print) -> Print
withOpts f = Print (\ o d -> doc (f o) o d)

var :: Var (LName Level) -> Print
var v = case v of
  Free (LName l n) -> P.pretty n <> P.pretty (getLevel l)
  Global n         -> P.pretty n

nameVar :: Name -> (Print -> Print) -> Print
nameVar n b = withLevel (\ d -> incrLevel (b (var (Free (LName (getUsed d) n)))))

pattern :: Options Print -> Pattern Print -> Print
pattern opts@Options{..} = \case
  PWildcard -> P.pretty "_"
  PVar p    -> p
  PCon n fs -> foldl1 (P.surround P.space) (S.var (Global n):map (pattern opts) fs)
  PDict os  -> P.brackets (P.flatAlt P.space P.line <> commaSep (map (\ (n :=: v) -> rname n P.<+> P.equals P.<+> P.group v) os) <> P.flatAlt P.space P.line)

commaSep :: [Print] -> Print
commaSep = P.encloseSep mempty mempty (P.comma <> P.space)

clause :: Pattern Name -> (Pattern (Name :=: Print) -> Print) -> Print
clause p b = let p' = (\ n -> n :=: nameVar n id) <$> p in withOpts (`pattern` fmap def p') P.<+> P.pretty "->" P.<+> b p'

µ̃ :: Print
µ̃ = P.pretty "µ̃"
