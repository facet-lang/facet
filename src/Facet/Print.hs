{-# LANGUAGE TypeFamilies #-}
module Facet.Print
( getPrint
, Print(..)
, Precedence(..)
, ann
  -- * Core printers
, printType
, printTExpr
, printExpr
, printModule
  -- * Misc
, intro
, tintro
, meta
) where

import           Data.Foldable (foldl', toList)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Semigroup (stimes)
import qualified Data.Text as T
import           Data.Traversable (mapAccumL)
import qualified Facet.Core as C
import           Facet.Name as Name
import           Facet.Pretty (lower, upper)
import           Facet.Stack
import           Facet.Style
import           Facet.Syntax
import qualified Prettyprinter as PP
import           Silkscreen as P
import           Silkscreen.Printer.Prec hiding (Level)
import qualified Silkscreen.Printer.Prec as P
import           Silkscreen.Printer.Rainbow as P

getPrint :: Print -> PP.Doc Style
getPrint = runRainbow (annotate . Nest) 0 . runPrec Null . doc . group


data Print = Print { fvs :: FVs, doc :: Prec Precedence (Rainbow (PP.Doc Style)) }

instance Semigroup Print where
  Print v1 d1 <> Print v2 d2 = Print (v1 <> v2) (d1 <> d2)
  stimes n (Print v d) = Print (stimes n v) (stimes n d)

instance Monoid Print where
  mempty = Print mempty mempty

instance Vars Print where
  cons l d = Print (cons l (fvs d)) (doc d)
  bind l d = Print (bind l (fvs d)) (doc d)

instance Printer Print where
  type Ann Print = Style

  liftDoc0 a = Print mempty (liftDoc0 a)
  liftDoc1 f (Print v d) = Print v (liftDoc1 f d)
  liftDoc2 f (Print v1 d1) (Print v2 d2) = Print (v1 <> v2) (liftDoc2 f d1 d2)

  -- FIXME: these run everything twice which seems bad.
  -- but then again, laziness.
  column    f = Print (fvs (f 0))         (column    (doc . f))
  nesting   f = Print (fvs (f 0))         (nesting   (doc . f))
  pageWidth f = Print (fvs (f Unbounded)) (pageWidth (doc . f))

  enclosing (Print vl dl) (Print vr dr) (Print vx dx) = Print (vl <> vr <> vx) (enclosing dl dr dx)

  brackets (Print v d) = Print v (brackets d)
  braces   (Print v d) = Print v (braces   d)
  parens   (Print v d) = Print v (parens   d)
  angles   (Print v d) = Print v (angles   d)
  squotes  (Print v d) = Print v (squotes  d)
  dquotes  (Print v d) = Print v (dquotes  d)

instance PrecedencePrinter Print where
  type Level Print = Precedence

  -- FIXME: this is running things twice.
  askingPrec f = Print (fvs (f minBound)) (askingPrec (doc . f))
  localPrec f (Print v d) = Print v (localPrec f d)

instance Show Print where
  showsPrec p = showsPrec p . getPrint


data Precedence
  = Null
  | Ann
  | FnR
  | FnL
  | Comp
  | Expr
  | Pattern
  | AppL
  | AppR
  | Var
  deriving (Bounded, Eq, Ord, Show)

op :: (Printer p, Ann p ~ Style) => p -> p
op = annotate Op


arrow :: (Printer p, Ann p ~ Style) => p
arrow = op (pretty "->")

comp :: Print -> Print
comp
  = block
  . prec Comp

block :: Print -> Print
block
  = group
  . align
  . braces
  . enclose space space

commaSep :: [Print] -> Print
commaSep = encloseSep mempty mempty (comma <> space)

ann :: (PrecedencePrinter p, P.Level p ~ Precedence) => (p ::: p) -> p
ann (n ::: t) = align . prec Ann $ n </> group (align (colon <+> flatAlt space mempty <> t))


($$), (-->) :: Print -> Print -> Print
f $$ a = askingPrec $ \case
  AppL -> op
  _    -> group op
  where
  -- FIXME: lambdas get parenthesized on the left
  op = leftAssoc AppL AppR (\ f a -> f <> nest 2 (line <> a)) f a

(-->) = rightAssoc FnR FnL (\ a b -> group (align a) </> arrow <+> b)

($$*) :: Foldable t => Print -> t Print -> Print
($$*) = fmap group . foldl' ($$)


-- Core printers

printType :: Stack Print -> C.Type -> Print
printType env = printTExpr env . C.quote (Name.Level (length env))

printTExpr :: Stack Print -> C.TExpr -> Print
printTExpr env = \case
  C.TVar v                   -> C.unVar (group . qvar) (\ d -> fromMaybe (pretty (getIndex d)) $ env !? getIndex d) meta v
  C.TType                    -> annotate Type $ pretty "Type"
  C.TInterface               -> annotate Type $ pretty "Interface"
  C.TForAll (n ::: t) b      -> braces (ann (intro n d ::: printTExpr env t)) --> printTExpr (env :> intro n d) b
  C.TArrow (Nothing ::: a) b -> printTExpr env a --> printTExpr env b
  C.TArrow (Just n ::: a) b  -> parens (ann (intro n d ::: printTExpr env a)) --> printTExpr env b
  C.TComp s t                -> sig s <+> printTExpr env t
  C.TInst f t                -> group (printTExpr env f) $$ group (braces (printTExpr env t))
  C.TApp f a                 -> group (printTExpr env f) $$ group (printTExpr env a)
  C.TString                  -> annotate Type $ pretty "String"
  where
  d = Name.Level (length env)
  sig s = brackets (commaSep (map (printTExpr env) s))

printExpr :: Stack Print -> C.Expr -> Print
printExpr env = \case
  C.XVar v        -> C.unVar (group . qvar) (\ d' -> fromMaybe (pretty (getIndex d')) $ env !? getIndex d') meta v
  C.XTLam b       -> let v = tintro __ d in braces (braces v <+> arrow <+> printExpr (env :> v) b)
  C.XLam cs       -> comp (braces (commaSep (map clause cs)))
  C.XInst e t     -> printExpr env e $$ braces (printTExpr env t)
  C.XApp f a      -> printExpr env f $$ printExpr env a
  C.XCon (n :$ p) -> group (qvar n) $$* (group . printExpr env <$> p)
  C.XOp q         -> group (qvar q)
  C.XString s     -> annotate Lit $ pretty (show s)
  where
  d = Name.Level (length env)
  binding env p f = let ((_, env'), p') = mapAccumL (\ (d, env) n -> let v = local n d in ((succ d, env :> v), v)) (Name.Level (length env), env) p in f env' p'
  clause (p, b) = binding env p $ \ env' p' -> pat p' <+> arrow <+> printExpr env' b
  pat = \case
    C.PVar n         -> n
    C.PCon (n :$ ps) -> parens (hsep (annotate Con (pretty n):map pat (toList ps)))
    C.PEff q ps k    -> brackets (pretty q <+> hsep (map pat (toList ps)) <+> semi <+> k)

printModule :: C.Module -> Print
printModule (C.Module mname is _ ds) = module_
  mname
  (qvar (fromList [T.pack "Kernel"]:.:U (T.pack "Module")))
  (map (\ (C.Import n) -> import' n) is)
  (map def (Map.toList (C.decls ds)))
  where
  def (n, Nothing ::: t) = ann
    $   qvar (Nil:.:n)
    ::: printType Nil t
  def (n, Just d  ::: t) = ann
    $   qvar (Nil:.:n)
    ::: defn (printType Nil t
    :=: case d of
      C.DTerm b  -> printExpr Nil b
      C.DData cs -> annotate Keyword (pretty "data") <+> declList
        (map (\ (n :=: _ ::: _T) -> ann (cname n ::: printType Nil _T)) (C.scopeToList cs))
      C.DInterface os -> annotate Keyword (pretty "interface") <+> declList
        (map (\ (n :=: _ ::: _T) -> ann (cname n ::: printType Nil _T)) (C.scopeToList os))
      C.DModule ds -> block (concatWith (surround hardline) (map ((hardline <>) . def) (Map.toList (C.decls ds)))))
  declList = block . group . concatWith (surround (hardline <> comma <> space)) . map group
  import' n = pretty "import" <+> braces (setPrec Var (prettyMName n))
  module_ n t is ds = ann (setPrec Var (prettyMName n) ::: t) </> concatWith (surround hardline) (is ++ map (hardline <>) ds)
  defn (a :=: b) = group a <> hardline <> group b

intro, tintro :: Name -> Level -> Print
intro  n = name lower n . getLevel
tintro n = name upper n . getLevel
qvar (_ :.: n) = setPrec Var (pretty n)

meta :: Meta -> Print
meta (Meta m) = setPrec Var $ annotate (Name m) $ pretty '?' <> upper m

local  n d = name lower n (getLevel d)
cname    n = setPrec Var (annotate Con (pretty n))

name :: (Int -> Print) -> Name -> Int -> Print
name f n d = setPrec Var . annotate (Name d) $
  if n == __ then
    pretty '_' <> f d
  else
    pretty n
