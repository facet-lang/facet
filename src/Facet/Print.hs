{-# LANGUAGE TypeFamilies #-}
module Facet.Print
( getPrint
, Print(..)
, Precedence(..)
, Highlight(..)
, ann
  -- * Core printers
, printValue
, printComp
, printModule
  -- * Misc
, intro
, tintro
, mvar
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

-- FIXME: move this into Facet.Style or something instead.
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

-- FIXME: 🔥 this
data Var
  = TLocal Name Level
  | Local Name Level
  | Cons Name


printVar :: ((Int -> Print) -> Name -> Level -> Print) -> Var -> Print
printVar name = \case
  TLocal n d -> name upper n d
  Local  n d -> name lower n d
  Cons     n -> setPrec Var (annotate Con (pretty n))


-- Core printers

printValue :: Stack Print -> C.Value -> Print
printValue env = \case
  C.KType -> annotate Type $ pretty "Type"
  C.KInterface -> annotate Type $ pretty "Interface"
  C.TSusp t -> printComp env t
  C.ELam p b -> comp . nest 2 . group . commaSep $ map (clause env p) b
  -- FIXME: there’s no way of knowing if the quoted variable was a type or expression variable
  -- FIXME: should maybe print the quoted variable differently so it stands out.
  C.VNe (h :$ e) ->
    let elim h sp  Nil     = case sp Nil of
          Nil -> h
          sp  -> app h sp
        elim h sp  (es:>a) = elim h (sp . (:> fmap (printValue env) a)) es
        -- FIXME: this throws an exception when pretty-printing the metacontext because entries can depend on variables bound in the context
        h' = C.unVar (group . qvar) ((env !) . getIndex . levelToIndex d) (group . mvar) h
    in elim h' id e
  C.ECon (n :$ p) -> app (group (qvar n)) (fmap ((Ex,) . printValue env) p)
  C.EOp (q :$ sp) -> app (group (qvar q)) (fmap (fmap (printValue env)) sp)
  C.TString   -> annotate Type $ pretty "String"
  C.EString s -> annotate Lit $ pretty (show s)
  where
  d = Level (length env)

printComp :: Stack Print -> C.Comp -> Print
printComp env = \case
  C.TForAll t b ->
    let (vs, (_, b')) = splitr C.unBind' (d, C.TForAll t b)
        binding env (C.Binding p n s _T) =
          let _T' = maybe mempty (brackets . commaSep . map (printValue env)) s <> printValue env _T
          in  (env :> tvar env ((p, fromMaybe __ n) ::: _T'), (p, name p (fromMaybe __ n) (Level (length env)) ::: _T'))
        name p n d
          | n == __, Ex <- p = []
          | otherwise        = [tintro n d]
        (env', vs') = mapAccumL binding env vs
    in fn vs' (printComp env' b')
  C.TRet s _T -> sig s <+> printValue env _T
  where
  d = Level (length env)

  sig (C.Sig v s) = brackets (maybe mempty (\ v -> printValue env v <> pipe) v <> commaSep (map (printValue env) s))


printModule :: C.Module -> Print
printModule (C.Module mname is _ ds) = module_
  mname
  (qvar (fromList [T.pack "Kernel"]:.:U (T.pack "Module")))
  (map (\ (C.Import n) -> import' n) is)
  (map def (Map.toList (C.decls ds)))
  where
  def (n, Nothing ::: t) = ann
    $   qvar (Nil:.:n)
    ::: printComp Nil t
  def (n, Just d  ::: t) = ann
    $   qvar (Nil:.:n)
    ::: defn (printComp Nil t
    :=: case d of
      C.DTerm b  -> printValue Nil b
      C.DData cs -> annotate Keyword (pretty "data") <+> declList
        (map (\ (n :=: _ ::: _T) -> ann (var (Cons n) ::: printComp Nil _T)) (C.scopeToList cs))
      C.DInterface os -> annotate Keyword (pretty "interface") <+> declList
        (map (\ (n :=: _ ::: _T) -> ann (var (Cons n) ::: printComp Nil _T)) (C.scopeToList os))
      C.DModule ds -> block (concatWith (surround hardline) (map ((hardline <>) . def) (Map.toList (C.decls ds)))))
  declList = block . group . concatWith (surround (hardline <> comma <> space)) . map group
  import' n = pretty "import" <+> braces (enclose mempty mempty (setPrec Var (prettyMName n)))
  module_ n t is ds = ann (setPrec Var (prettyMName n) ::: t) </> concatWith (surround hardline) (is ++ map (hardline <>) ds)
  defn (a :=: b) = group a <> hardline <> group b

intro, tintro :: Name -> Level -> Print
intro = name lower
tintro = name upper
qvar (_ :.: n) = setPrec Var (pretty n)

mvar :: (PrecedencePrinter p, P.Level p ~ Precedence, Ann p ~ Highlight) => Meta -> p
mvar m = setPrec Var (annotate (Hole m) (pretty '?' <> upper (getMeta m)))

var = printVar name
name f n d = setPrec Var . annotate (Name d) $
  if n == __ then
    pretty '_' <> f (getLevel d)
  else
    pretty n

-- FIXME: group quantifiers by kind again.
fn = flip (foldr (\ (pl, n ::: _T) b -> case n of
  [] -> _T --> b
  _  -> ((pl, group (commaSep n)) ::: _T) >~> b))
tvar env n = group (var (TLocal (snd (tm n)) (Level (length env))))
app f as = group f $$* fmap (group . uncurry (unPl braces id)) as

lvar env (p, n) = var (unPl TLocal Local p n (Level (length env)))

clause env pl (C.Clause p b) = unPl brackets id pl (pat (fst <$> p')) <+> arrow <+> printValue env' (b (snd <$> p'))
  where
  ((_, env'), p') = mapAccumL (\ (d, env) (n ::: _) -> let v = lvar env (pl, n) in ((succ d, env :> v), (v, C.free d))) (Level (length env), env) p
pat = \case
  C.PVar n         -> n
  C.PCon (n :$ ps) -> parens (hsep (annotate Con (pretty n):map pat (toList ps)))
  C.PEff q ps k    -> brackets (pretty q <+> hsep (map pat (toList ps)) <+> semi <+> k)
