{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Print
( getPrint
, Print(..)
, Precedence(..)
, ann
  -- * Options
, Options(..)
, verboseOptions
, quietOptions
, qualified
, unqualified
, printInstantiation
, suppressInstantiation
  -- * Core printers
, printType
, printTExpr
, printValue
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
import qualified Data.Text as T
import           Data.Traversable (mapAccumL)
import qualified Facet.Core.Module as C
import qualified Facet.Core.Term as C
import qualified Facet.Core.Term as CE
import qualified Facet.Core.Type as C
import qualified Facet.Core.Type as CT
import           Facet.Name as Name
import           Facet.Pretty (lower, upper)
import           Facet.Semiring (one, zero)
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
  { qname         :: Q Name -> Print
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

qualified, unqualified :: Q Name -> Print
qualified = pretty
unqualified (_:.:n) = pretty n

printInstantiation, suppressInstantiation :: Print -> Print -> Print
printInstantiation = ($$)
suppressInstantiation = const


-- Core printers

printType :: Options -> Stack Print -> C.Type -> Print
printType opts env = printTExpr opts env . CT.quote (Name.Level (length env))

printTExpr :: Options -> Stack Print -> C.TExpr -> Print
printTExpr Options{ qname, instantiation } = go
  where
  qvar = group . setPrec Var . qname
  go env = \case
    C.TVar (C.TGlobal n)    -> qvar n
    C.TVar (C.TFree d)      -> fromMaybe (pretty (getIndex d)) $ env !? getIndex d
    C.TVar (C.TMetavar m)   -> meta m
    C.TType                 -> annotate Type $ pretty "Type"
    C.TInterface            -> annotate Type $ pretty "Interface"
    C.TForAll      n    t b -> braces (ann (intro n d ::: go env t)) --> go (env :> intro n d) b
    C.TArrow Nothing  q a b -> mult q (go env a) --> go env b
    C.TArrow (Just n) q a b -> parens (ann (intro n d ::: mult q (go env a))) --> go env b
    C.TSusp t               -> braces (go env t)
    C.TRet [] t             -> go env t
    C.TRet s t              -> sig s <+> go env t
    C.TInst f t             -> group (go env f) `instantiation` group (braces (go env t))
    C.TApp f a              -> group (go env f) $$ group (go env a)
    C.TString               -> annotate Type $ pretty "String"
    where
    d = Name.Level (length env)
    sig s = brackets (commaSep (map (go env) s))
    mult q = if
      | q == zero -> (pretty '0' <+>)
      | q == one  -> (pretty '1' <+>)
      | otherwise -> id

printValue :: Options -> Stack Print -> C.Value -> Print
printValue opts env = printExpr opts env . CE.quote (Name.Level (length env))

printExpr :: Options -> Stack Print -> C.Expr -> Print
printExpr opts@Options{ qname, instantiation } = go
  where
  go env = \case
    C.XVar (C.Global n) -> qvar n
    C.XVar (C.Free d')  -> fromMaybe (pretty (getIndex d')) $ env !? getIndex d'
    C.XTLam b           -> let { d = Name.Level (length env) ; v = tintro __ d } in braces (braces v <+> arrow <+> go (env :> v) b)
    C.XLam cs           -> comp (commaSep (map (clause env) cs))
    C.XInst e t         -> go env e `instantiation` braces (printTExpr opts env t)
    C.XApp f a          -> go env f $$ go env a
    C.XCon n t p        -> foldl' instantiation (qvar n) (group . braces . printTExpr opts env <$> t) $$* (group . go env <$> p)
    C.XOp q             -> qvar q
    C.XString s         -> annotate Lit $ pretty (show s)
  qvar = group . setPrec Var . qname
  binding env p f = let ((_, env'), p') = mapAccumL (\ (d, env) n -> let v = local n d in ((succ d, env :> v), v)) (Name.Level (length env), env) p in f env' p'
  clause env (p, b) = binding env p $ \ env' p' -> pat p' <+> arrow <+> go env' b
  vpat = \case
    C.PWildcard -> pretty '_'
    C.PVar n    -> n
    C.PCon n ps -> parens (hsep (annotate Con (qname n):map vpat (toList ps)))
  pat = \case
    C.PAll n      -> brackets n
    C.PVal p      -> vpat p
    C.PEff q ps k -> brackets (pretty q <+> hsep (map vpat (toList ps)) <+> semi <+> k)

printModule :: C.Module -> Print
printModule (C.Module mname is _ ds) = module_
  mname
  (qvar (fromList [T.pack "Kernel"]:.:U (T.pack "Module")))
  (map (\ (C.Import n) -> import' n) is)
  (map def (Map.toList (C.decls ds)))
  where
  def (n, Nothing ::: t) = ann
    $   qvar (Nil:.:n)
    ::: printType opts Nil t
  def (n, Just d  ::: t) = ann
    $   qvar (Nil:.:n)
    ::: defn (printType opts Nil t
    :=: case d of
      C.DTerm b  -> printValue opts Nil b
      C.DData cs -> annotate Keyword (pretty "data") <+> declList
        (map (\ (n :=: _ ::: _T) -> ann (cname n ::: printType opts Nil _T)) (C.scopeToList cs))
      C.DInterface os -> annotate Keyword (pretty "interface") <+> declList
        (map (\ (n :=: _ ::: _T) -> ann (cname n ::: printType opts Nil _T)) (C.scopeToList os))
      C.DModule ds -> block (concatWith (surround hardline) (map ((hardline <>) . def) (Map.toList (C.decls ds)))))
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
cname    n = setPrec Var (annotate Con (pretty n))

name :: (Int -> Print) -> Name -> Int -> Print
name f n d = setPrec Var . annotate (Name d) $
  if n == __ then
    pretty '_' <> f d
  else
    pretty n
