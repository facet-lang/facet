{-# LANGUAGE TypeFamilies #-}
module Facet.Print
( getPrint
, Print(..)
, Precedence(..)
, ann
  -- * Core printers
, printValue
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

(>~>) :: ((Icit, Print) ::: Print) -> Print -> Print
((pl, n) ::: t) >~> b = prec FnR (flatAlt (column (\ i -> nesting (\ j -> stimes (j + 3 - i) space))) mempty <> group (align (unPl braces parens pl (space <> ann (setPrec Var n ::: t) <> line))) </> arrow <+> b)


-- Core printers

printValue :: Stack Print -> C.Value -> Print
printValue env = \case
  C.VKType -> annotate Type $ pretty "Type"
  C.VKInterface -> annotate Type $ pretty "Interface"
  C.VTForAll t b ->
    let (vs, (_, b')) = splitr C.unBind' (d, C.VTForAll t b)
        binding env (C.Binding p n _T) =
          let _T' = printValue env _T
          in  (env :> tvar env ((p, fromMaybe __ n) ::: _T'), (p, name p (fromMaybe __ n) (Name.Level (length env)) ::: _T'))
        name p n d
          | n == __, Ex <- p = []
          | otherwise        = [tintro n d]
        (env', vs') = mapAccumL binding env vs
    in fn vs' (printValue env' b')
  C.VTComp s t -> sig s <+> printValue env t
  C.VELam p b -> comp . nest 2 . group . commaSep $ map (clause env p) b
  C.VNe (h :$ e) ->
    let elim h sp  Nil     = case sp Nil of
          Nil -> h
          sp  -> app h sp
        elim h sp  (es:>a) = elim h (sp . (:> fmap (printValue env) a)) es
        h' = C.unVar (group . qvar) (\ d' -> fromMaybe (pretty (getLevel d')) $ env !? getIndex (levelToIndex d d')) meta h
    in elim h' id e
  C.VECon (n :$ p) -> app (group (qvar n)) (fmap ((Ex,) . printValue env) p)
  C.VEOp (q :$ sp) -> app (group (qvar q)) (fmap (fmap (printValue env)) sp)
  C.VTString   -> annotate Type $ pretty "String"
  C.VEString s -> annotate Lit $ pretty (show s)
  where
  d = Name.Level (length env)
  sig (C.Sig v s) = brackets (printValue env v <> pipe <> commaSep (map (printValue env) s))


printModule :: C.Module -> Print
printModule (C.Module mname is _ ds) = module_
  mname
  (qvar (fromList [T.pack "Kernel"]:.:U (T.pack "Module")))
  (map (\ (C.Import n) -> import' n) is)
  (map def (Map.toList (C.decls ds)))
  where
  def (n, Nothing ::: t) = ann
    $   qvar (Nil:.:n)
    ::: printValue Nil t
  def (n, Just d  ::: t) = ann
    $   qvar (Nil:.:n)
    ::: defn (printValue Nil t
    :=: case d of
      C.DTerm b  -> printValue Nil b
      C.DData cs -> annotate Keyword (pretty "data") <+> declList
        (map (\ (n :=: _ ::: _T) -> ann (cname n ::: printValue Nil _T)) (C.scopeToList cs))
      C.DInterface os -> annotate Keyword (pretty "interface") <+> declList
        (map (\ (n :=: _ ::: _T) -> ann (cname n ::: printValue Nil _T)) (C.scopeToList os))
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

tlocal n d = name upper n (getLevel d)
local  n d = name lower n (getLevel d)
cname    n = setPrec Var (annotate Con (pretty n))

name :: (Int -> Print) -> Name -> Int -> Print
name f n d = setPrec Var . annotate (Name d) $
  if n == __ then
    pretty '_' <> f d
  else
    pretty n

-- FIXME: group quantifiers by kind again.
fn = flip (foldr (\ (pl, n ::: _T) b -> case n of
  [] -> _T --> b
  _  -> ((pl, group (commaSep n)) ::: _T) >~> b))
tvar env n = group (tlocal (snd (tm n)) (Name.Level (length env)))
app f as = group f $$* fmap (group . uncurry (unPl braces id)) as

lvar env (p, n) = unPl tlocal local p n (Name.Level (length env))

clause env pl (C.Clause p b) = unPl brackets id pl (pat (fst <$> p')) <+> arrow <+> printValue env' (b (snd <$> p'))
  where
  ((_, env'), p') = mapAccumL (\ (d, env) n -> let v = lvar env (pl, n) in ((succ d, env :> v), (v, C.free d))) (Name.Level (length env), env) p
pat = \case
  C.PVar n         -> n
  C.PCon (n :$ ps) -> parens (hsep (annotate Con (pretty n):map pat (toList ps)))
  C.PEff q ps k    -> brackets (pretty q <+> hsep (map pat (toList ps)) <+> semi <+> k)
