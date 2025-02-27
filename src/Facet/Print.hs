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
, printSubject
, printKind
, printType
, printInterface
, printTExpr
, printNorm
, printExpr
, printPattern
, printModule
  -- * Misc
, intro
, tintro
, meta
) where

import           Data.Foldable (toList)
import           Data.Maybe (fromMaybe)
import qualified Data.Text as T
import           Data.Traversable (mapAccumL)
import qualified Facet.Core.Module as C
import           Facet.Core.Pattern
import qualified Facet.Core.Term as C
import qualified Facet.Core.Type as C
import qualified Facet.Core.Type as CT
import           Facet.Env as Env
import           Facet.Name as Name
import qualified Facet.Norm as N
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

-- FIXME: add an option to control whether shifts are printed
data Options = Options
  { rname         :: RName -> Print
  , instantiation :: Print -> Print -> Print
  }

verboseOptions :: Options
verboseOptions = Options
  { rname         = qualified
  , instantiation = printInstantiation
  }

quietOptions :: Options
quietOptions = Options
  { rname         = unqualified
  , instantiation = suppressInstantiation
  }

qualified, unqualified :: RName -> Print
qualified = pretty
unqualified (_:.:n) = pretty n

printInstantiation, suppressInstantiation :: Print -> Print -> Print
printInstantiation = ($$)
suppressInstantiation = const


-- Core printers

printSubject :: Options -> Env Print -> C.Classifier -> Print
printSubject opts env = \case
  C.CK k -> printKind env k
  C.CT t -> printType opts env t

printKind :: Env Print -> C.Kind -> Print
printKind env = \case
  C.KType               -> annotate Type $ pretty "Type"
  C.KInterface          -> annotate Type $ pretty "Interface"
  C.KArrow Nothing  a b -> printKind env a --> printKind env b
  C.KArrow (Just n) a b -> parens (ann (intro n d ::: printKind env a)) --> printKind env b
  where
  d = level env

printType :: Options -> Env Print -> C.Type -> Print
printType opts env = printTExpr opts env . CT.quote (level env)

printInterface :: Options -> Env Print -> C.Interface C.Type -> Print
printInterface = printInterfaceWith printType

printTExpr :: Options -> Env Print -> C.TExpr -> Print
printTExpr opts@Options{ rname } = go
  where
  qvar = group . setPrec Var . rname
  go env = \case
    C.TVar (Global n)       -> qvar n
    C.TVar (Free (Right n)) -> fromMaybe (lname (indexToLevel d <$> n)) $ Env.lookup env n
    C.TVar (Free (Left m))  -> meta m
    C.TForAll      n    t b -> braces (ann (intro n d ::: printKind env t)) --> go (env |> pvar (n :=: intro n d)) b
    C.TArrow Nothing  q a b -> mult q (go env a) --> go env b
    C.TArrow (Just n) q a b -> parens (ann (intro n d ::: mult q (go env a))) --> go env b
    C.TComp s t             -> if s == mempty then go env t else sig s <+> go env t
    C.TApp f a              -> group (go env f) $$ group (go env a)
    C.TString               -> annotate Type $ pretty "String"
    where
    d = level env
    sig s = brackets (commaSep (map (interface env) (C.interfaces s)))
  interface = printInterfaceWith printTExpr opts
  mult q = if
    | q == zero -> (pretty '0' <+>)
    | q == one  -> (pretty '1' <+>)
    | otherwise -> id

printInterfaceWith :: (Options -> Env Print -> a -> Print) -> Options -> Env Print -> C.Interface a -> Print
printInterfaceWith with opts@Options{ rname } env (C.Interface h sp) = rname h $$* fmap (with opts env) sp

printNorm :: Options -> Env Print -> N.Norm -> Print
printNorm opts env = printExpr opts env . N.quote (level env)

printExpr :: Options -> Env Print -> C.Expr -> Print
printExpr opts@Options{ rname, instantiation } = go
  where
  go env = \case
    C.XVar (Global n) -> qvar n
    C.XVar (Free n)   -> fromMaybe (lname (indexToLevel d <$> n)) $ Env.lookup env n
    C.XTLam n b       -> let { d = level env ; v = tintro n d } in braces (braces v <+> arrow <+> go (env |> pvar (__ :=: v)) b)
    C.XInst e t       -> go env e `instantiation` braces (printTExpr opts env t)
    C.XLam cs         -> comp (commaSep (map (clause env) cs))
    C.XApp f a        -> go env f $$ go env a
    C.XCon n p        -> qvar n $$* (group . go env <$> p)
    C.XOp n p         -> qvar n $$* (group . go env <$> p)
    C.XString s       -> annotate Lit $ pretty (show s)
    where
    d = level env
  qvar = group . setPrec Var . rname
  clause env (p, b) = printPattern opts (def <$> p') <+> arrow <+> go (env |> p') b
    where
    p' = snd (mapAccumL (\ d n -> (succ d, n :=: local n d)) (level env) p)

printPattern :: Options -> Pattern Print -> Print
printPattern Options{ rname } = \case
  PVal p -> vpat p
  PEff p -> epat p
  where
  vpat = \case
    PWildcard -> pretty '_'
    PVar n    -> n
    PCon n ps -> parens (hsep (annotate Con (rname n):map vpat (toList ps)))
  epat = \case
    PAll n     -> n
    POp q ps k -> brackets (hsep (pretty q : map vpat (toList ps)) <+> semi <+> k)

printModule :: C.Module -> Print
printModule (C.Module mname is _ ds) = module_
  mname
  (qvar (fromList [T.pack "Kernel"]:.U (T.pack "Module")))
  (map (\ (C.Import n) -> import' n) is)
  (map def (C.scopeToList ds))
  where
  def (n :=: d) = ann
    $   qvar (Nil:.n)
    ::: case d of
      C.DTerm Nothing  _T ->       printType opts empty _T
      C.DTerm (Just b) _T -> defn (printType opts empty _T :=: printExpr opts empty b)
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

qvar :: (P.Level p ~ Precedence, PrecedencePrinter p) => QName -> p
qvar (_ :. n) = setPrec Var (pretty n)

lname :: LName Level -> Print
lname (LName d n) = intro n d

meta :: Meta -> Print
meta (Meta m) = setPrec Var $ annotate (Name m) $ pretty '?' <> upper m

local :: Name -> Level -> Print
local  n d = name lower n (getLevel d)

name :: (Int -> Print) -> Name -> Int -> Print
name f n d = setPrec Var . annotate (Name d) $
  if n == __ then
    pretty '_' <> f d
  else
    pretty n
