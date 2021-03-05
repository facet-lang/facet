{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Print
( getPrint
, Print(..)
, Precedence(..)
, ann
, ($$)
, ($$*)
  -- * Options
, Options(..)
, verboseOptions
, quietOptions
, qualified
, unqualified
, printInstantiation
, suppressInstantiation
  -- * Core printers
, printKind
, printNType
, printPType
, printNTExpr
, printPTExpr
, printExpr
, printModule
  -- * Misc
, intro
, tintro
, meta
) where

import           Data.Foldable (foldl', toList)
import           Data.Maybe (fromMaybe)
import qualified Data.Text as T
import           Data.Traversable (mapAccumL)
import qualified Facet.Core.Module as C
import qualified Facet.Core.Term as C
import qualified Facet.Core.Type as C
import qualified Facet.Core.Type as CT
import           Facet.Name as Name
import           Facet.Pretty (lower, upper)
import           Facet.Semiring (one, zero)
import           Facet.Snoc
import           Facet.Style
import           Facet.Syntax
import qualified Prettyprinter as PP
import           Silkscreen as P
import           Silkscreen.Printer.Prec hiding (Level)
import qualified Silkscreen.Printer.Prec as P
import           Silkscreen.Printer.Rainbow as P

getPrint :: Print -> PP.Doc Style
getPrint = runRainbow (annotate . Nest) 0 . runPrec Null . doc . group


newtype Print = Print { doc :: Prec Precedence (Rainbow (PP.Doc Style)) }
  deriving (Monoid, PrecedencePrinter, Printer, Semigroup)

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
  | Shift
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


-- Options

data Options = Options
  { qname         :: QName -> Print
  , instantiation :: Print -> Print -> Print
  }

verboseOptions :: Options
verboseOptions = Options
  { qname         = qualified
  , instantiation = printInstantiation
  }

quietOptions :: Options
quietOptions = Options
  { qname         = unqualified
  , instantiation = suppressInstantiation
  }

qualified, unqualified :: QName -> Print
qualified = pretty
unqualified (_:.:n) = pretty n

printInstantiation, suppressInstantiation :: Print -> Print -> Print
printInstantiation = ($$)
suppressInstantiation = const


-- Core printers

printKind :: Options -> Level -> C.Kind -> Print
printKind Options{ qname } d = go
  where
  go = \case
    C.Type                -> annotate Type $ pretty "Type"
    C.Interface           -> annotate Type $ pretty "Interface"
    C.KArrow Nothing  a b -> go a --> go b
    C.KArrow (Just n) a b -> parens (ann (intro n d ::: go a)) --> go b
    C.KSpine h sp         -> group (qname h) $$* (group . go <$> sp)

printNType :: Options -> Snoc Print -> C.NType -> Print
printNType opts env = printNTExpr opts env . CT.quoteN (Name.Level (length env))

printPType :: Options -> Snoc Print -> C.PType -> Print
printPType opts env = printPTExpr opts env . CT.quoteP (Name.Level (length env))

printNTExpr :: Options -> Snoc Print -> C.NTExpr -> Print
printNTExpr = fst . printTExpr

printPTExpr :: Options -> Snoc Print -> C.PTExpr -> Print
printPTExpr = snd . printTExpr

printTExpr :: Options -> (Snoc Print -> C.NTExpr -> Print, Snoc Print -> C.PTExpr -> Print)
printTExpr opts@Options{ qname } = (goN, goP)
  where
  qvar = group . setPrec Var . qname
  goN env = \case
    C.TArrow  Nothing  q a b -> mult q (goP env a) --> goN env b
    C.TArrow  (Just n) q a b -> parens (ann (intro n d ::: mult q (goP env a))) --> goN env b
    C.TComp [] t             -> prec Shift $ pretty '↑' <+> goP env t
    C.TComp s t              -> prec Shift $ pretty '↑' <+> sig s <+> goP env t
    where
    d = Name.Level (length env)
    sig :: [C.Interface] -> Print
    sig s = brackets (commaSep (map (printKind opts d . C.getInterface) s))
    mult q = if
      | q == zero -> (pretty '0' <+>)
      | q == one  -> (pretty '1' <+>)
      | otherwise -> id
  goP env = \case
    C.TForAll       n    t b -> braces (ann (intro n d ::: printKind opts d t)) --> goP (env :> intro n d) b
    C.TVar (Global n)        -> qvar n
    C.TVar (Free d)          -> fromMaybe (pretty (getIndex d)) $ env !? getIndex d
    C.TVar (Metavar m)       -> meta m
    C.TString                -> annotate Type $ pretty "String"
    C.TThunk t               -> prec Shift $ pretty '↓' <+> goN env t
    C.TApp f a               -> group (goP env f) $$ group (goP env a)
    where
    d = Name.Level (length env)

printExpr :: Options -> Snoc Print -> C.Expr -> Print
printExpr opts@Options{ qname, instantiation } = go
  where
  go env = \case
    C.XVar (Global n)  -> qvar n
    C.XVar (Free d')   -> fromMaybe (pretty (getIndex d')) $ env !? getIndex d'
    C.XVar (Metavar m) -> case m of {}
    C.XTLam b          -> braces (braces v <+> arrow <+> go (env :> v) b)
    C.XInst e t        -> go env e `instantiation` braces (printPTExpr opts env t)
    C.XLam cs          -> comp (commaSep (map (clause env) cs))
      where
      clause env (p, b) = binding env p $ \ env' p' -> pat p' <+> arrow <+> go env' b
    C.XApp f a         -> go env f $$ go env a
    C.XCon n t p       -> foldl' instantiation (qvar n) (group . braces . printPTExpr opts env <$> t) $$* (group . go env <$> p)
    C.XOp n t p        -> pretty '#' <> brackets (foldl' instantiation (qvar n) (group . braces . printPTExpr opts env <$> t) $$* (group . go env <$> p))
    C.XString s        -> annotate Lit $ pretty (show s)
    -- FIXME: add options controlling printing of shifts &c.
    C.XForce t         -> go env t <> pretty '!'
    C.XThunk c         -> braces (go env c)
    C.XReturn v        -> go env v
    -- FIXME: maybe print as @x <- a; b@ instead?
    C.XBind a b        -> go env a <+> pretty "to" <+> v <+> dot <+> go (env :> v) b
    where
    d = Name.Level (length env)
    v = tintro __ d
  qvar = group . setPrec Var . qname
  binding env p f = let ((_, env'), p') = mapAccumL (\ (d, env) n -> let v = local n d in ((succ d, env :> v), v)) (Name.Level (length env), env) p in f env' p'
  vpat = \case
    C.PWildcard -> pretty '_'
    C.PVar n    -> n
    C.PCon n ps -> parens (hsep (annotate Con (qname n):map vpat (toList ps)))
  epat = \case
    C.PAll n     -> n
    C.POp q ps k -> brackets (pretty q <+> hsep (map vpat (toList ps)) <+> semi <+> k)
  pat = \case
    C.PVal p -> vpat p
    C.PEff p -> epat p

printModule :: C.Module -> Print
printModule (C.Module mname is _ ds) = module_
  mname
  (qvar (fromList [T.pack "Kernel"]:.:N (T.pack "Module")))
  (map (\ (C.Import n) -> import' n) is)
  (map def (C.scopeToList ds))
  where
  def (n :=: d) = ann
    $   qvar (Nil:.:n)
    ::: case d of
      C.DTerm Nothing        _T ->       printPType opts Nil _T
      C.DTerm (Just (Pos b)) _T -> defn (printPType opts Nil _T :=: printExpr opts Nil b)
      C.DData cs _K -> annotate Keyword (pretty "data") <+> declList
        (map def (C.scopeToList cs))
      C.DInterface os _K -> annotate Keyword (pretty "interface") <+> declList
        (map def (C.scopeToList os))
      C.DModule ds _K -> block (concatWith (surround hardline) (map ((hardline <>) . def) (C.scopeToList ds)))
  declList = block . group . concatWith (surround (hardline <> comma <> space)) . map group
  import' n = pretty "import" <+> braces (setPrec Var (prettyMName n))
  module_ n t is ds = ann (setPrec Var (prettyMName n) ::: t) </> concatWith (surround hardline) (is ++ map (hardline <>) ds)
  defn (a :=: b) = group a <> hardline <> group b
  opts = quietOptions

intro, tintro :: Name -> Level -> Print
intro  n = name lower n . getLevel
tintro n = name upper n . getLevel
qvar (_ :.: n) = setPrec Var (pretty n)

meta :: Meta -> Print
meta (Meta m) = setPrec Var $ annotate (Name m) $ pretty '?' <> upper m

local  n d = name lower n (getLevel d)

name :: (Int -> Print) -> Name -> Int -> Print
name f n d = setPrec Var . annotate (Name d) $
  if n == __ then
    pretty '_' <> f d
  else
    pretty n
