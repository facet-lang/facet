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
  -- * Misc
, intro
, tintro
, meta
  -- * Printable
, Printable(..)
, Printable1(..)
, print1
) where

import           Data.Foldable (foldl', toList)
import           Data.Maybe (fromMaybe)
import qualified Data.Text as T
import           Data.Traversable (mapAccumL)
import           Facet.Env as Env
import           Facet.Interface
import           Facet.Kind
import qualified Facet.Module as C
import           Facet.Name as Name
import           Facet.Pattern
import           Facet.Pretty (lower, upper)
import           Facet.Quote
import           Facet.Semiring (one, zero)
import           Facet.Snoc
import           Facet.Style
import           Facet.Syntax
import qualified Facet.Term.Expr as C
import qualified Facet.Term.Norm as N
import qualified Facet.Type.Expr as TX
import qualified Facet.Type.Norm as TN
import           Prelude hiding (print)
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


intro, tintro :: Name -> Level -> Print
intro  n = name lower n . getLevel
tintro n = name upper n . getLevel
qvar (_ :. n) = setPrec Var (pretty n)

lname :: LName Level -> Print
lname (LName d n) = intro n d

meta :: Meta -> Print
meta (Meta m) = setPrec Var $ annotate (Name m) $ pretty '?' <> upper m

local  n d = name lower n (getLevel d)

name :: (Int -> Print) -> Name -> Int -> Print
name f n d = setPrec Var . annotate (Name d) $
  if n == __ then
    pretty '_' <> f d
  else
    pretty n


-- Printable

class Printable t where
  print :: Options -> Env Print -> t -> Print

instance Printable Print where
  print _ _ = id

instance (Quote v t, Printable t) => Printable (Quoting t v) where
  print opts env = print opts env . quote (level env) . getQuoting

instance Printable TN.Classifier where
  print opts env = \case
    TN.CK k -> print opts env k
    TN.CT t -> print opts env t

instance Printable Kind where
  print opts env = \case
    KType               -> annotate Type $ pretty "Type"
    KInterface          -> annotate Type $ pretty "Interface"
    KArrow Nothing  a b -> print opts env a --> print opts env b
    KArrow (Just n) a b -> parens (ann (intro n d ::: print opts env a)) --> print opts env b
    where
    d = level env

instance Printable a => Printable (Interface a) where
  print = print1

instance Printable TX.Type where
  print opts@Options{ rname } = go
    where
    qvar = group . setPrec Var . rname
    go env = \case
      TX.Var (Global n)       -> qvar n
      TX.Var (Free (Right n)) -> fromMaybe (lname (indexToLevel d <$> n)) $ Env.lookup env n
      TX.Var (Free (Left m))  -> meta m
      TX.ForAll      n    t b -> braces (ann (intro n d ::: print opts env t)) --> go (env |> PVar (n :=: intro n d)) b
      TX.Arrow Nothing  q a b -> mult q (go env a) --> go env b
      TX.Arrow (Just n) q a b -> parens (ann (intro n d ::: mult q (go env a))) --> go env b
      TX.Comp s t             -> if s == mempty then go env t else sig s <+> go env t
      TX.App f a              -> group (go env f) $$ group (go env a)
      TX.String               -> annotate Type $ pretty "String"
      where
      d = level env
      sig s = brackets (commaSep (map (interface env) (interfaces s)))
    interface = printWith print opts
    mult q = if
      | q == zero -> (pretty '0' <+>)
      | q == one  -> (pretty '1' <+>)
      | otherwise -> id

deriving via (Quoting TX.Type TN.Type) instance Printable TN.Type


instance Printable C.Expr where
  print opts@Options{ rname } = go
    where
    go env = \case
      C.Var (Global n) -> qvar n
      C.Var (Free n)   -> fromMaybe (lname (indexToLevel d <$> n)) $ Env.lookup env n
      C.Lam cs         -> comp (commaSep (map (clause env) cs))
      C.App f a        -> go env f $$ go env a
      C.Con n p        -> qvar n $$* (group . go env <$> p)
      C.String s       -> annotate Lit $ pretty (show s)
      C.Dict os        -> brackets (flatAlt space line <> commaSep (map (\ (n :=: v) -> rname n <+> equals <+> group (go env v)) os) <> flatAlt space line)
      C.Let p v b      -> let p' = snd (mapAccumL (\ d n -> (succ d, n :=: local n d)) (level env) p) in pretty "let" <+> braces (print opts env (def <$> p') </> equals <+> group (go env v)) <+> pretty "in" <+> go (env |> p') b
      C.Comp p b       -> comp (clause env (PDict p, b))
      where
      d = level env
    qvar = group . setPrec Var . rname
    clause env (p, b) = print opts env (def <$> p') <+> arrow <+> go (env |> p') b
      where
      p' = snd (mapAccumL (\ d n -> (succ d, n :=: local n d)) (level env) p)

deriving via (Quoting C.Expr N.Norm) instance Printable N.Norm

instance Printable a => Printable (Pattern a) where
  print = print1


instance Printable C.Module where
  print opts env (C.Module mname is _ ds) = module_
    mname
    (qvar (fromList [U (T.pack "Kernel")]:.U (T.pack "Module")))
    (map (\ (C.Import n) -> import' n) is)
    (map (def . fmap defBody) (C.scopeToList ds))
    where
    def (n :=: d) = ann (qvar (Nil:.n) ::: d)
    defBody = \case
      C.DTerm Nothing  _T ->       print opts env _T
      C.DTerm (Just b) _T -> defn (print opts env _T :=: print opts env b)
      C.DData cs _K       -> annotate Keyword (pretty "data") <+> scope defBody cs
      C.DInterface os _K  -> annotate Keyword (pretty "interface") <+> scope (print opts env) os
      C.DModule ds _K     -> block (concatWith (surround hardline) (map ((hardline <>) . def . fmap defBody) (C.scopeToList ds)))
    scope with = block . group . concatWith (surround (hardline <> comma <> space)) . map (group . def . fmap with) . C.scopeToList
    import' n = pretty "import" <+> braces (setPrec Var (prettyMName n))
    module_ n t is ds = ann (setPrec Var (prettyMName n) ::: t) </> concatWith (surround hardline) (is ++ map (hardline <>) ds)
    defn (a :=: b) = group a <> hardline <> group b


class Printable1 f where
  printWith :: (Options -> Env Print -> a -> Print) -> Options -> Env Print -> f a -> Print

instance Printable1 Interface where
  printWith with opts@Options{ rname } env (Interface h sp) = rname h $$* fmap (with opts env) sp

instance Printable1 Pattern where
  printWith with opts@Options{ rname } env = go
    where
    go = \case
      PWildcard -> pretty '_'
      PVar n    -> with opts env n
      PCon n ps -> parens (annotate Con (rname n) $$* map go (toList ps))
      PDict os  -> brackets (flatAlt space line <> commaSep (map (\ (n :=: v) -> rname n <+> equals <+> group (with opts env v)) os) <> flatAlt space line)


print1 :: (Printable1 f, Printable a) => Options -> Env Print -> f a -> Print
print1 = printWith print
