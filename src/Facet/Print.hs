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
, Printable2(..)
) where

import           Data.Foldable (foldl')
import           Data.Maybe (fromMaybe)
import qualified Data.Text as T
import           Facet.Env as Env
import           Facet.Interface
import           Facet.Kind
import qualified Facet.Module as C
import           Facet.Name as Name hiding (name)
import           Facet.Pattern
import           Facet.Pretty (lower, upper)
import           Facet.Print.Options
import           Facet.Quote
import qualified Facet.Scope as C
import           Facet.Snoc
import           Facet.Snoc.NonEmpty (NonEmpty(..))
import           Facet.Style
import           Facet.Syntax hiding (Ann(..))
import qualified Facet.Term.Expr as C
import qualified Facet.Term.Norm as N
import qualified Facet.Type.Expr as TX
import qualified Facet.Type.Norm as TN
import           Fresnel.Getter (view)
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


intro, tintro :: Name -> Level -> Print
intro  n = name lower n . getLevel
tintro n = name upper n . getLevel

qvar :: (P.Level p ~ Precedence, PrecedencePrinter p) => QName -> p
qvar (_ :|> n) = setPrec Var (pretty n)

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


-- Printable

class Printable t where
  print :: Options Print -> Env Print -> t -> Print

instance Printable Print where
  print _ _ = id

instance (Quote v t, Printable t) => Printable (Quoting t v) where
  print opts env = print opts env . runQuoter (level env) . quote . getQuoting

instance Printable Kind where
  print opts env = \case
    KType               -> annotate Type $ pretty "Type"
    KInterface          -> annotate Type $ pretty "Interface"
    KArrow Nothing  a b -> print opts env a --> print opts env b
    KArrow (Just n) a b -> parens (ann (intro n (level env) ::: print opts env a)) --> print opts env b

instance Printable a => Printable (Interface a) where
  print = print1

instance Printable TX.Type where
  print opts@Options{ qname } = go
    where
    qvar = group . setPrec Var . qname
    go env = \case
      TX.Var (Global n)       -> qvar n
      TX.Var (Free (Right n)) -> fromMaybe (intro __ (toLeveled d n)) $ Env.lookup env (LName n __)
      TX.Var (Free (Left m))  -> meta m
      TX.ForAll      n  t b   -> braces (ann (intro n d ::: print opts env t)) --> go (env |> PVal (PVar (n :=: intro n d))) b
      TX.Arrow Nothing  a b   -> go env a --> go env b
      TX.Arrow (Just n) a b   -> parens (ann (intro n d ::: go env a)) --> go env b
      TX.Comp s t             -> if s == mempty then go env t else sig s <+> go env t
      TX.App f a              -> group (go env f) $$ group (go env a)
      TX.String               -> annotate Type $ pretty "String"
      where
      d = level env
      sig s = brackets (commaSep (map (interface env) (interfaces s)))
    interface = printWith print opts

deriving via (Quoting TX.Type TN.Type) instance Printable TN.Type


instance Printable C.Term where
  print opts@Options{ qname } = go
    where
    go env = \case
      C.Var (Global n) -> qvar n
      C.Var (Free n)   -> fromMaybe (lname (toLeveled d n)) $ Env.lookup env n
      C.Lam cs         -> comp (commaSep (map (clause env) cs))
      C.App f a        -> go env f $$ go env a
      C.Con n p        -> qvar n $$* (group . go env <$> p)
      C.String s       -> annotate Lit $ pretty (show s)
      C.Let p v b      -> let p' = snd (mapAccumLevels (\ d n -> n :=: local n d) (level env) p) in pretty "let" <+> braces (print opts env (view def_ <$> p') </> equals <+> group (go env v)) <+> pretty "in" <+> go (env |> p') b
      where
      d = level env
    qvar = group . setPrec Var . qname
    clause env (p, b) = print opts env (view def_ <$> p') <+> arrow <+> go (env |> p') b
      where
      p' = snd (mapAccumLevels (\ d n -> n :=: local n d) (level env) p)

deriving via (Quoting C.Term N.Term) instance Printable N.Term

instance Printable a => Printable (Pattern a) where
  print = print1


instance Printable C.Module where
  print opts env (C.Module mname is _ ds) = module_
    mname
    (qvar (fromList [T (T.pack "Kernel")]:|>T (T.pack "Module")))
    (map (\ (C.Import n) -> import' n) is)
    (map (def . fmap defBody) (view C.toList_ ds))
    where
    def (n :=: d) = ann (qvar (Nil:|>n) ::: d)
    defBody = \case
      C.DTerm Nothing  _T ->       print opts env _T
      C.DTerm (Just b) _T -> defn (print opts env _T :=: print opts env b)
      C.DSubmodule s _K   -> case s of
        C.SData cs      -> annotate Keyword (pretty "data") <+> scope (print opts env) cs
        C.SInterface os -> annotate Keyword (pretty "interface") <+> scope (print opts env) os
        C.SModule ds    -> block (concatWith (surround hardline) (map ((hardline <>) . def . fmap defBody) (view C.toList_ ds)))
    scope with = block . group . concatWith (surround (hardline <> comma <> space)) . map (group . def . fmap with) . view C.toList_
    import' n = pretty "import" <+> braces (setPrec Var (prettyQName n))
    module_ n t is ds = ann (setPrec Var (prettyQName n) ::: t) </> concatWith (surround hardline) (is ++ map (hardline <>) ds)
    defn (a :=: b) = group a <> hardline <> group b


class Printable1 f where
  printWith :: (Options Print -> Env Print -> a -> Print) -> Options Print -> Env Print -> f a -> Print

instance Printable1 Interface where
  printWith with opts@Options{ qname } env (Interface h sp) = qname h $$* fmap (with opts env) sp

instance Printable1 ValPattern where
  printWith with opts@Options{ qname } env = go
    where
    go = \case
      PWildcard -> pretty '_'
      PVar n    -> with opts env n
      PCon n ps -> parens (annotate Con (qname n) $$* map go ps)

instance Printable1 EffPattern where
  printWith with opts@Options{ qname } env (POp n ps k) = brackets (qname n $$* map (printWith with opts env) ps <+> pretty ';' <+> printWith with opts env k)

instance Printable1 Pattern where
  printWith with opts env = \case
    PVal p -> printWith with opts env p
    PEff p -> printWith with opts env p


print1 :: (Printable1 f, Printable a) => Options Print -> Env Print -> f a -> Print
print1 = printWith print


class Printable2 p where
  printWith2
    :: (Options Print -> Env Print -> a     -> Print)
    -> (Options Print -> Env Print ->     b -> Print)
    -> (Options Print -> Env Print -> p a b -> Print)


instance Printable2 (,) where
  printWith2 f g opts env (a, b) = tupled [f opts env a, g opts env b]

instance Printable2 Either where
  printWith2 f g opts env = either (f opts env) (g opts env)


print2 :: (Printable2 p, Printable a, Printable b) => Options Print -> Env Print -> p a b -> Print
print2 = printWith2 print print
