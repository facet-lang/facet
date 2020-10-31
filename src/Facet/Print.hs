{-# LANGUAGE TypeFamilies #-}
module Facet.Print
( getPrint
, Print(..)
, Precedence(..)
, Highlight(..)
, ann
  -- * Core printers
, printValue
, printTelescope
, printModule
  -- * Misc
, intro
, tintro
) where

import           Data.Foldable (foldl', toList)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Semigroup (stimes)
import qualified Data.Text as T
import           Data.Traversable (mapAccumL)
import qualified Facet.Core as C
import           Facet.Name
import           Facet.Pretty (lower, upper)
import           Facet.Stack
import           Facet.Syntax
import qualified Prettyprinter as PP
import           Silkscreen as P
import           Silkscreen.Printer.Prec hiding (Level)
import qualified Silkscreen.Printer.Prec as P
import           Silkscreen.Printer.Rainbow as P

getPrint :: Print -> PP.Doc Highlight
getPrint = runRainbow (annotate . Nest) 0 . runPrec Null . doc . group


data Print = Print { fvs :: FVs, doc :: Prec Precedence (Rainbow (PP.Doc Highlight)) }

instance Semigroup Print where
  Print v1 d1 <> Print v2 d2 = Print (v1 <> v2) (d1 <> d2)
  stimes n (Print v d) = Print (stimes n v) (stimes n d)

instance Monoid Print where
  mempty = Print mempty mempty

instance Vars Print where
  cons l d = Print (cons l (fvs d)) (doc d)
  bind l d = Print (bind l (fvs d)) (doc d)

instance Printer Print where
  type Ann Print = Highlight

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

data Highlight
  = Nest Int
  | Name Level
  | Keyword
  | Con
  | Type
  | Op
  | Lit
  | Hole Meta
  deriving (Eq, Show)

op :: (Printer p, Ann p ~ Highlight) => p -> p
op = annotate Op


arrow :: (Printer p, Ann p ~ Highlight) => p
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

(>~>) :: ((Pl, Print) ::: Print) -> Print -> Print
((pl, n) ::: t) >~> b = prec FnR (flatAlt (column (\ i -> nesting (\ j -> stimes (j + 3 - i) space))) mempty <> group (align (unPl braces parens pl (space <> ann (setPrec Var n ::: t) <> line))) </> arrow <+> b)


-- Algebras

data Var
  = Global (Maybe MName) DName
  | TLocal UName Level
  | Local UName Level
  | Metavar Meta
  | Cons UName

qvar :: QName -> Var
qvar (m :.: n) = Global (Just m) n


printVar :: ((Int -> Print) -> UName -> Level -> Print) -> Var -> Print
printVar name = \case
  Global _ n -> setPrec Var (pretty n)
  TLocal n d -> name upper n d
  Local  n d -> name lower n d
  Metavar  m -> setPrec Var (annotate (Hole m) (pretty '?' <> upper (getMeta m)))
  Cons     n -> setPrec Var (annotate Con (pretty n))


-- Core printers

printValue :: Stack Print -> C.Value -> Print
printValue env = \case
  C.VType -> annotate Type $ pretty "Type"
  C.VInterface -> annotate Type $ pretty "Interface"
  C.VComp t -> printTelescope env t
  C.VLam p b -> comp . nest 2 . group . commaSep $ map (clause env p) b
  -- FIXME: there’s no way of knowing if the quoted variable was a type or expression variable
  -- FIXME: should maybe print the quoted variable differently so it stands out.
  C.VNe (h :$ e) ->
    let elim h sp  Nil     = case sp Nil of
          Nil -> h
          sp  -> app h sp
        elim h sp  (es:>a) = elim h (sp . (:> fmap (printValue env) a)) es
        h' = C.unVar (group . var . qvar) ((env !) . getIndex . levelToIndex d) (group . var . Metavar) h
    in elim h' id e
  C.VCon (n :$ p) -> app (group (var (qvar n))) (fmap ((Ex,) . printValue env) p)
  C.VOp (q :$ sp) -> app (group (var (qvar q))) (fmap (fmap (printValue env)) sp)
  C.VPrim p -> case p of
    C.TString   -> annotate Type $ pretty "String"
    C.VString s -> annotate Lit $ pretty (show s)
  where
  d = Level (length env)

printTelescope :: Stack Print -> C.Comp -> Print
printTelescope env = \case
  C.ForAll t b ->
    let (vs, (_, b')) = splitr C.unBind' (d, C.ForAll t b)
        binding env (C.Binding p n s _T) =
          let _T' = sig env s _T
          in  (env :> tvar env ((p, fromMaybe __ n) ::: _T'), (p, name p (fromMaybe __ n) (Level (length env)) ::: _T'))
        name p n d
          | T.null (getUName n)
          , Ex <- p             = []
          | otherwise           = [tintro n d]
        (env', vs') = mapAccumL binding env vs
    in fn vs' (printTelescope env' b')
  C.Comp s _T -> sig env s _T
  where
  d = Level (length env)


printModule :: C.Module -> Print
printModule (C.Module mname is _ ds) = module_
  $   mname
  ::: Just (var (Global (Just (MName (T.pack "Kernel"))) (T (UName (T.pack "Module")))))
  :=: (map (\ (C.Import n) -> import' n) is, map def (Map.toList ds))
  where
  def (n, C.Decl Nothing  t) = ann
    $   var (Global (Just mname) n)
    ::: printTelescope Nil t
  def (n, C.Decl (Just d) t) = ann
    $   var (Global (Just mname) n)
    ::: defn (printTelescope Nil t
    :=: case d of
      C.DTerm b  -> printValue Nil b
      C.DData cs -> annotate Keyword (pretty "data") <+> declList
        (map (\ (n :=: _ ::: _T) -> ann (var (Cons n) ::: printTelescope Nil _T)) cs)
      C.DInterface os -> annotate Keyword (pretty "interface") <+> declList
        (map (\ (n ::: _T) -> ann (var (Cons n) ::: printTelescope Nil _T)) os))
  declList = block . group . concatWith (surround (hardline <> comma <> space)) . map group
  import' n = pretty "import" <+> braces (enclose mempty mempty (setPrec Var (pretty n)))
  module_ (n ::: t :=: (is, ds)) = ann (setPrec Var (pretty n) ::: fromMaybe (pretty "Module") t) </> concatWith (surround hardline) (is ++ map (hardline <>) ds)
  defn (a :=: b) = group a <> hardline <> group b

intro, tintro :: UName -> Level -> Print
intro = name lower
tintro = name upper
var = printVar name
name f n d = setPrec Var . annotate (Name d) $
  if T.null (getUName n) then
    pretty '_' <> f (getLevel d)
  else
    pretty n

-- FIXME: group quantifiers by kind again.
fn = flip (foldr (\ (pl, n ::: _T) b -> case n of
  [] -> _T --> b
  _  -> ((pl, group (commaSep n)) ::: _T) >~> b))
tvar env n = group (var (TLocal (snd (tm n)) (Level (length env))))
sig env s _T = tcomp (map (printValue env) <$> s) (printValue env _T)
app f as = group f $$* fmap (group . uncurry (unPl braces id)) as
tcomp s t = case s of
  Nothing -> t
  Just s  -> brackets (commaSep s) <+> t

lvar env (p, n) = var (unPl TLocal Local p n (Level (length env)))

clause env pl (C.Clause p b) = unPl brackets id pl (pat (fst <$> p')) <+> arrow <+> printValue env' (b (snd <$> p'))
  where
  ((_, env'), p') = mapAccumL (\ (d, env) (n ::: _) -> let v = lvar env (pl, n) in ((succ d, env :> v), (v, C.free d))) (Level (length env), env) p
pat = \case
  C.PVar n         -> n
  C.PCon (n :$ ps) -> parens (hsep (annotate Con (pretty n):map pat (toList ps)))
  C.PEff q ps k    -> brackets (pretty q <+> hsep (map pat (toList ps)) <+> semi <+> k)
