{-# LANGUAGE TypeFamilies #-}
module Facet.Print
( prettyPrint
, getPrint
, terminalStyle
, Print(..)
, Precedence(..)
, ann
, printContextEntry
  -- * Algebras
, surface
, explicit
) where

import           Control.Monad.IO.Class
import           Data.Colour.RGBSpace.HSL
import           Data.Foldable (foldl', toList)
import           Data.Function (on)
import           Data.Maybe (fromMaybe)
import           Data.Semigroup (stimes)
import qualified Data.Text as T
import           Facet.Algebra
import           Facet.Name hiding (ann)
import           Facet.Pretty
import           Facet.Syntax
import qualified Prettyprinter as PP
import           Silkscreen as P
import           Silkscreen.Printer.Prec hiding (Level)
import qualified Silkscreen.Printer.Prec as P
import           Silkscreen.Printer.Rainbow as P

prettyPrint :: MonadIO m => Print -> m ()
prettyPrint = putDoc . getPrint

getPrint :: Print -> PP.Doc [SGR]
getPrint = PP.reAnnotate terminalStyle . getPrint'

getPrint' :: Print -> PP.Doc Highlight
getPrint' = runRainbow (annotate . Nest) 0 . runPrec Null . doc . group

terminalStyle :: Highlight -> [SGR]
terminalStyle = \case
  Nest i -> [setRGB (pick i 0.4 0.8)]
  Name i -> [setRGB (pick (-getLevel i) 0.8 0.6)]
  Op     -> [setRGB (hsl 180 0.7 0.4)]
  Type   -> [setRGB (hsl 60 0.5 0.5)]
  Con    -> [setRGB (hsl 15 0.8 0.5)]
  Lit    -> [setBold]
  Hole m -> [setBold, setRGB (pick (-getMeta m) 0.5 0.45)]
  where
  pick i s l = hsl (fromIntegral i * phi * 30) s l
  phi = 1.618033988749895


data Print = Print { fvs :: FVs, doc :: Prec Precedence (Rainbow (PP.Doc Highlight)) }

instance Semigroup Print where
  Print v1 d1 <> Print v2 d2 = Print (v1 <> v2) (d1 <> d2)
  stimes n (Print v d) = Print (stimes n v) (stimes n d)

instance Monoid Print where
  mempty = Print mempty mempty

instance Vars Print where
  use l = Print (use l) mempty
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

-- FIXME: NO. BAD.
instance Eq Print where
  (==) = (==) `on` show


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


printContextEntry :: Level -> UName ::: Print -> Print
printContextEntry l (n ::: _T) = ann (intro explicit n l ::: _T)


($$), (-->) :: Print -> Print -> Print
f $$ a = askingPrec $ \case
  AppL -> op
  _    -> group op
  where
  -- FIXME: lambdas get parenthesized on the left
  op = leftAssoc AppL AppR (\ f a -> f <> nest 2 (line <> a)) f a

-- FIXME: I think the precedence is being reset by the parens or something and thus we aren’t parenthesizing the body?
(-->) = rightAssoc FnR FnL (\ a b -> group (align a) </> arrow <+> b)

($$*) :: Foldable t => Print -> t Print -> Print
($$*) = fmap group . foldl' ($$)

(>~>) :: ((Pl, Print) ::: Print) -> Print -> Print
((pl, n) ::: t) >~> b = prec FnR (flatAlt (column (\ i -> nesting (\ j -> stimes (j + 3 - i) space))) mempty <> group (align (unPl braces parens pl (space <> ann (setPrec Var n ::: t) <> line))) </> arrow <+> b)


-- FIXME: these are poorly factored. Most of the structure can be shared, we just want to override a few in each.
surface :: Algebra Print
surface = Algebra
  { var = \case
    Global _ n -> setPrec Var (pretty n)
    TLocal n d -> name upper n d
    Local  n d -> name lower n d
    Quote  n d -> stimes (3 :: Int) $ name lower n d
    Metavar  m -> setPrec Var (annotate (Hole m) (pretty '?' <> upper (getMeta m)))
    Cons     n -> setPrec Var (annotate Con (pretty n))
  , tintro = name upper
  , intro = name lower
  , lam = comp . embed . commaSep
  , clause = \ ns b -> embed (setPrec Pattern (vsep (map (unPl_ (braces . tm) tm) ns)) </> arrow) </> b
  -- FIXME: group quantifiers by kind again.
  , fn = \ as b -> foldr (\ (P pl (n ::: _T)) b -> case n of
    Just n -> ((pl, n) ::: _T) >~> b
    _      -> _T --> b) b as
  , app = \ f as -> f $$* fmap (unPl_ braces id) as
  , hole = \ n -> annotate (Hole (Meta 0)) $ pretty '?' <> pretty n
  , _Type = annotate Type $ pretty "Type"
  , _Void = annotate Type $ pretty "Void"
  , ann' = tm
  , case' = \ s ps -> align . group $ pretty "case" <+> setPrec Expr s </> block (concatWith (surround (hardline <> comma <> space)) (map (group . (\ (p, b) -> align (embed (prec Pattern p </> arrow) </> b))) ps))
  , pcon = \ n ps -> parens (hsep (annotate Con n:toList ps))
  , tuple = tupled
  , decl = ann
  , defn = \ (a :=: b) -> a </> b
  , data' = block . group . concatWith (surround (hardline <> comma <> space)) . map group
  , module_ = \ (n ::: t :=: (is, ds)) -> ann (setPrec Var (pretty n) ::: fromMaybe (pretty "Module") t) </> block (embed (concatWith (surround hardline) (is ++ map (hardline <>) ds)))
  , import' = \ n -> pretty "import" <+> braces (enclose mempty mempty (setPrec Var (pretty n)))
  }
  where
  embed = nest 2 . group
  name f n d = setPrec Var . annotate (Name d) $ if T.null (getUName n) then
    pretty '_' <> f (getLevel d)
  else
    pretty n

-- FIXME: elide unused vars
explicit :: Algebra Print
explicit = Algebra
  { var = \case
    Global _ n -> setPrec Var (pretty n)
    TLocal n d -> name upper n d
    Local  n d -> name lower n d
    Quote  n d -> stimes (3 :: Int) $ name lower n d
    Metavar  m -> setPrec Var (annotate (Hole m) (pretty '?' <> upper (getMeta m)))
    Cons     n -> setPrec Var (annotate Con (pretty n))
  , tintro = name upper
  , intro = name lower
  , lam = comp . embed . commaSep
  , clause = \ ns b -> group (align (setPrec Pattern (vsep (map (\ (P pl (n ::: _T)) -> group $ unPl braces id pl (maybe n (ann . (n :::)) _T)) ns)) </> arrow)) </> b
  -- FIXME: group quantifiers by kind again.
  , fn = \ as b -> foldr (\ (P pl (n ::: _T)) b -> case n of
    Just n -> ((pl, n) ::: _T) >~> b
    _      -> _T --> b) b as
  , app = \ f as -> group f $$* fmap (group . unPl_ braces id) as
  , hole = \ n -> annotate (Hole (Meta 0)) $ pretty '?' <> pretty n
  , _Type = annotate Type $ pretty "Type"
  , _Void = annotate Type $ pretty "Void"
  , ann' = group . tm
  , case' = \ s ps -> align . group $ pretty "case" <+> setPrec Expr s </> block (concatWith (surround (hardline <> comma <> space)) (map (group . (\ (p, b) -> align (embed (prec Pattern p </> arrow) </> b))) ps))
  , pcon = \ n ps -> parens (hsep (annotate Con n:toList ps))
  , tuple = tupled
  , decl = ann
  , defn = \ (a :=: b) -> group a <> hardline <> group b
  , data' = block . group . concatWith (surround (hardline <> comma <> space)) . map group
  , module_ = \ (n ::: t :=: (is, ds)) -> ann (setPrec Var (pretty n) ::: fromMaybe (pretty "Module") t) </> block (embed (concatWith (surround hardline) (is ++ map (hardline <>) ds)))
  , import' = \ n -> pretty "import" <+> braces (enclose mempty mempty (setPrec Var (pretty n)))
  }
  where
  embed = nest 2 . group
  name f _ d = setPrec Var (annotate (Name d) (cons d (f (getLevel d))))
