{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Sequent.Print
( Print(..)
) where

import           Facet.Name
import           Facet.Pattern (Pattern(..))
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
  µR n b = P.pretty "µ" <> P.braces (nameVar n id P.<+> P.dot P.<+> nameVar n b)
  funR cs = P.braces (P.encloseSep (P.flatAlt P.space mempty) (P.flatAlt P.space mempty) (P.comma <> P.space) (map (uncurry clause) cs))
  conR n fs = foldl1 (P.surround P.space) (S.var (Global n):fs)
  stringR = P.pretty . show
  dictR os = withOpts (\ Options{..} -> P.brackets (P.flatAlt P.space P.line <> commaSep (map (\ (n :=: v) -> rname n P.<+> P.equals P.<+> P.group v) os) <> P.flatAlt P.space P.line))
  compR p b = P.group
    . P.align
    . P.braces
    . P.enclose P.space P.space $ clause (PDict p) b

  covar = var
  µL n b = P.pretty "µ̃" <> P.braces (P.pretty n P.<+> P.dot P.<+> withLevel (\ d -> b (var (Free (LName (getUsed d) n)))))
  funL a k = a P.<+> P.dot P.<+> k

  (.|.) = fmap (P.enclose P.langle P.rangle) . P.surround P.pipe

withLevel :: (Used -> Print) -> Print
withLevel f = Print (\ o d -> doc (f d) o d)

incrLevel :: Print -> Print
incrLevel p = Print (\ o -> doc p o . succ)

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
