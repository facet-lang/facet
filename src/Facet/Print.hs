{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Print
( prettyPrint
, getPrint
, terminalStyle
, Print(..)
, Precedence(..)
, evar
, tvar
  -- * Interpreters
, printCoreValue
, printContextEntry
, printSurfaceType
, printSurfaceExpr
, printSurfaceClause
, printCorePattern
, printSurfacePattern
, printSurfaceDecl
, printCoreModule
, printSurfaceModule
  -- * Algebras
, surface
, explicit
) where

import           Control.Applicative ((<**>))
import           Control.Category ((>>>))
import           Control.Monad.IO.Class
import           Data.Bifunctor (bimap, first)
import           Data.Bitraversable (bimapAccumL)
import           Data.Foldable (foldl', toList)
import           Data.Function (on)
import qualified Data.IntSet as IntSet
import           Data.List (intersperse)
import           Data.List.NonEmpty (NonEmpty)
import           Data.Maybe (fromMaybe)
import           Data.Semigroup (stimes)
import qualified Data.Text as T
import           Facet.Algebra
import qualified Facet.Core as C
import           Facet.Name hiding (ann)
import qualified Facet.Pretty as P
import           Facet.Stack
import qualified Facet.Surface as S
import           Facet.Syntax
import           Prelude hiding ((**))
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import           Silkscreen as P
import           Silkscreen.Printer.Prec hiding (Level)
import qualified Silkscreen.Printer.Prec as P
import           Silkscreen.Printer.Rainbow as P
import           Text.Parser.Position

prettyPrint :: MonadIO m => Print -> m ()
prettyPrint = P.putDoc . getPrint

getPrint :: Print -> PP.Doc ANSI.AnsiStyle
getPrint = PP.reAnnotate terminalStyle . getPrint'

getPrint' :: Print -> PP.Doc Highlight
getPrint' = runRainbow (annotate . Nest) 0 . runPrec Null . doc . group

terminalStyle :: Highlight -> ANSI.AnsiStyle
terminalStyle = \case
  Nest i -> colours !! (i `mod` len)
  Name i -> reverse colours !! (getLevel i `mod` len)
  Op     -> ANSI.color ANSI.Cyan
  Type   -> ANSI.color ANSI.Yellow
  Con    -> ANSI.color ANSI.Red
  Lit    -> ANSI.bold
  Hole   -> ANSI.bold <> ANSI.color ANSI.Black
  ANSI s -> s
  where
  colours =
    [ ANSI.Red
    , ANSI.Green
    , ANSI.Yellow
    , ANSI.Blue
    , ANSI.Magenta
    , ANSI.Cyan
    ]
    <**>
    [ANSI.color, ANSI.colorDull]
  len = length colours


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

  -- NB: FIXME: these run everything twice which seems bad.
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
  | Hole
  | ANSI ANSI.AnsiStyle
  deriving (Eq, Ord, Show)

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

evar :: (PrecedencePrinter p, P.Level p ~ Precedence, Ann p ~ Highlight) => Level -> p
evar = setPrec Var . annotate . Name <*> P.lower . getLevel

tvar :: (PrecedencePrinter p, P.Level p ~ Precedence, Ann p ~ Highlight) => Level -> p
tvar = setPrec Var . annotate . Name <*> P.upper . getLevel


prettyMName :: Printer p => MName -> p
prettyMName (n :. s)  = prettyMName n <> pretty '.' <> pretty s
prettyMName (MName s) = pretty s

prettyQName :: PrecedencePrinter p => QName -> p
prettyQName (mname :.: n) = prettyMName mname <> pretty '.' <> pretty n


printCoreValue ::  Level -> C.Value Print -> Print
printCoreValue = go
  where
  go d = \case
    C.Type     -> _Type
    C.Void     -> _Void
    C.TUnit    -> _Unit
    C.Unit     -> _Unit
    t C.:=> b  ->
      let n' = name d
          t' = go d (ty t)
          b' = go (succ d) (b (C.free n'))
      in if IntSet.member (getLevel d) (getFVs (fvs b')) then
        ((pl (tm t), n') ::: t') >~> bind d b'
      else
        unPl braces id (pl (tm t)) t' --> bind d b'
    C.Lam n b  ->
      let (vs, (d', b')) = splitr (C.unLam' (cons <*> var' True)) (d, C.Lam n b)
          b'' = go d' b'
      in lam (map (\ (d, n) -> var' (IntSet.member (getLevel d) (getFVs (fvs b''))) d n) vs) b''
    -- FIXME: there’s no way of knowing if the quoted variable was a type or expression variable
    -- FIXME: should maybe print the quoted variable differently so it stands out.
    C.Neut h e -> group $ foldl' (elim d) (C.unHead (ann . bimap cglobal (go d)) id tvar (ann . bimap (annotate Hole . (pretty '?' <>) . evar) (go d)) h) e
    C.TPrd l r -> go d l ** go d r
    C.Prd  l r -> go d l ** go d r
    C.VCon n p -> ann (bimap cglobal (go d) n) $$* fmap (go d) p
  name d = cons d (tvar d)
  clause d (p, b) =
    let (d', p') = bimapAccumL (\ d' v -> (d', go d v)) (\ d' (_ ::: _T) -> (succ d', ann (evar d' ::: go d _T))) d p
        b' = foldr bind (go d' (b (bimap C.free C.free p'))) [d..d']
    in nest 2 $ group (prec Pattern (printCorePattern p') </> arrow) </> b'
  elim d f = \case
    C.App  a -> f $$ unPl_ (braces . go d) (go d) a
    C.Case p -> nest 2 $ group $ pretty "case" <+> setPrec Expr f </> block (commaSep (map (clause d) p))

  var' u d (n ::: _T) = group . align $ unPl braces id (pl n) $ ann $ setPrec Var (annotate (Name d) (p <> unPl tvar evar (pl n) d)) ::: printCoreValue d _T
    where
    p | u         = mempty
      | otherwise = pretty '_'

  lam vs b = block $ nest 2 $ group (setPrec Pattern (vsep vs) </> arrow) </> b

  _Type = annotate Type $ pretty "Type"
  _Void = annotate Type $ pretty "Void"
  _Unit = annotate Type $ pretty "Unit"


printContextEntry :: Level -> UName ::: Print -> Print
printContextEntry l (n ::: _T) = ann (cbound n l ::: _T)


printSurfaceType :: Stack Print -> Spanned (S.Type a) -> Print
printSurfaceType = go
  where
  go env = snd >>> \case
    S.TFree n  -> sglobal n
    S.TBound n -> env ! getIndex n
    S.THole n  -> hole n
    S.Type     -> _Type
    S.Void     -> _Void
    S.TUnit    -> _Unit
    t S.:=> b ->
      let (t', b') = splitr (S.unForAll . snd) b
      in forAlls (map (first sbound) (t:t')) (go (env:>sbound (tm t)) b')
    f S.:$$ a ->
      let (f', a') = splitl (S.unTApp . snd) f
      in go env f' $$* fmap (go env) (a' :> a)
    a S.:-> b -> go env a --> go env b
    l S.:** r -> go env l **  go env r
  _Type = annotate Type $ pretty "Type"
  _Void = annotate Type $ pretty "Void"
  _Unit = annotate Type $ pretty "Unit"
  hole n = annotate Hole $ pretty '?' <> pretty n


sglobal :: Pretty n => n -> Print
sglobal = setPrec Var . pretty

cglobal :: QName -> Print
cglobal = setPrec Var . prettyQName


sbound :: UName -> Print
sbound = setPrec Var . pretty

cbound :: UName -> Level -> Print
cbound h level = cons level (h' <> pretty (getLevel level))
  where
  h'
    | T.null (getUName h) = pretty '_'
    | otherwise           = pretty h


($$), (-->), (**) :: Print -> Print -> Print
f $$ a = askingPrec $ \case
  AppL -> op
  _    -> group op
  where
  -- FIXME: lambdas get parenthesized on the left
  op = leftAssoc AppL AppR (\ f a -> f <> nest 2 (line <> a)) f a

-- FIXME: I think the precedence is being reset by the parens or something and thus we aren’t parenthesizing the body?
(-->) = rightAssoc FnR FnL (\ a b -> group (align a) </> arrow <+> b)

-- FIXME: left-flatten products
l ** r = tupled [l, r]

($$*) :: Foldable t => Print -> t Print -> Print
($$*) = fmap group . foldl' ($$)

(>~>) :: ((Pl, Print) ::: Print) -> Print -> Print
((pl, n) ::: t) >~> b = prec FnR (flatAlt (column (\ i -> nesting (\ j -> stimes (j + 3 - i) space))) mempty <> group (align (unPl braces parens pl (space <> ann (setPrec Var n ::: t) <> line))) </> arrow <+> b)

forAlls :: [Print ::: Spanned (S.Type a)] -> Print -> Print
forAlls ts b = foldr go b (groupByType S.aeq ts)
  where
  -- FIXME: this is horribly wrong and probably going to crash
  go (t, ns) b = ((Im, commaSep ns) ::: printSurfaceType Nil t) >~> b

groupByType :: (t -> t -> Bool) -> [n ::: Spanned t] -> [(Spanned t, [n])]
groupByType eq = \case
  []   -> []
  (n ::: t):xs -> (t, n:map tm ys) : groupByType eq zs
    where
    (ys,zs) = span (eq (snd t) . snd . ty) xs


printSurfaceExpr :: Stack Print -> Spanned (S.Expr a) -> Print
printSurfaceExpr = go
  where
  go env = snd >>> \case
    S.Free n  -> sglobal n
    S.Bound n -> env ! getIndex n
    S.Hole n  -> hole n
    f S.:$  a ->
      let (f', a') = splitl (S.unApp . snd) f
      in go env f' $$* fmap (go env) (a' :> a)
    S.Unit    -> unit
    l S.:*  r -> go env l **  go env r
    S.Comp c  -> comp $ case snd c of
      S.Expr e     -> prec Expr $ printSurfaceExpr env e
      S.Clauses cs -> commaSep (map (uncurry (printSurfaceClause env)) cs)
  hole n = annotate Hole $ pretty '?' <> pretty n
  unit = annotate Con $ pretty "Unit"

printSurfaceClause :: Stack Print -> NonEmpty (Spanned (S.Pattern UName)) -> Spanned (S.Expr a) -> Print
printSurfaceClause env ps b = foldMap printSurfacePattern ps' <+> arrow <> group (nest 2 (line <> prec Expr (printSurfaceExpr env' b)))
  where
  ps' = fmap (fmap sbound) <$> ps
  env' = foldl (foldl (foldl (:>))) env ps'

printCorePattern :: C.Pattern Print Print -> Print
printCorePattern = \case
  C.Wildcard -> pretty '_'
  C.Var n    -> n
  C.Con n ps -> parens (hsep (annotate Con (ann (first prettyQName n)):map printCorePattern ps))
  C.Tuple p  -> tupled (map printCorePattern p)

printSurfacePattern :: Spanned (S.Pattern Print) -> Print
printSurfacePattern p = prec Pattern $ case snd p of
  S.Wildcard -> pretty '_'
  S.Var n    -> n
  S.Con n ps -> parens (hsep (annotate Con (pretty n):map printSurfacePattern ps))
  S.Tuple p  -> tupled (map printSurfacePattern p)

printSurfaceData :: Stack Print -> [Spanned (CName ::: Spanned (S.Type a))] -> Print
printSurfaceData env cs = block . commaSep $ map (ann . bimap (annotate Con . pretty) (printSurfaceType env) . snd) cs


printSurfaceDecl :: Spanned (S.Decl a) -> Print
printSurfaceDecl = go Nil
  where
  go env = snd >>> \case
    t S.:=   b -> printSurfaceType env t .= case b of
      S.DExpr e -> printSurfaceExpr env e
      S.DType t -> printSurfaceType env t
      S.DData c -> printSurfaceData env c
    t S.:==> b ->
      let (t', b') = splitr (S.unDForAll . snd) b
          ts = map (first sbound) (t:t')
      in forAlls ts (go (foldl (\ as (a:::_) -> as :> a) env ts) b')
    t S.:--> b -> bimap sbound (printSurfaceType env) t >-> go (env:>sbound (tm t)) b


-- FIXME: it would be nice to ensure that this gets wrapped if the : in the same decl got wrapped.
(.=) :: Print -> Print -> Print
t .= b = t </> b

(>->) :: (Print ::: Print) -> Print -> Print
(n ::: t) >-> b = prec FnR (group (align (parens (ann (n ::: t)))) </> arrow <+> b)


printCoreModule :: C.Module Print -> Print
printCoreModule (C.Module n ds)
  = module' n $ map (\ (n, d ::: t) -> ann (cglobal n ::: printCoreValue (Level 0) t) </> printCoreDef d) ds

printCoreDef :: C.Def Print -> Print
printCoreDef = \case
  C.DTerm b  -> printCoreValue (Level 0) b
  C.DType b  -> printCoreValue (Level 0) b
  C.DData cs -> block . commaSep $ map (ann . bimap (annotate Con . pretty) (printCoreValue (Level 0))) cs


printSurfaceModule :: Spanned (S.Module a) -> Print
printSurfaceModule (_, S.Module n ds) = module' n (map (uncurry printSurfaceDef . snd) ds)

printSurfaceDef :: DName -> Spanned (S.Decl a) -> Print
printSurfaceDef n d = def (sglobal n) (printSurfaceDecl d)


module' :: MName -> [Print] -> Print
module' n b = ann (setPrec Var (prettyMName n) ::: pretty "Module") </> block (nest 2 (vsep (intersperse mempty b)))

def :: Print -> Print -> Print
def n b = group $ ann (n ::: b)


surface :: Algebra Print
surface = Algebra
  { var = \case
    Global _ n -> setPrec Var (pretty n)
    TLocal n d -> name P.upper n d
    Local  n d -> name P.lower n d
    Meta     d -> setPrec Var (annotate Hole (pretty '?' <> evar d))
    Cons     n -> setPrec Var (annotate Con (pretty n))
  , tintro = name P.upper
  , intro = name P.lower
  , lam = comp . embed . commaSep
  , clause = \ ns b -> embed (setPrec Pattern (vsep (map (unPl_ (braces . tm) tm) ns)) </> arrow) </> b
  -- FIXME: group quantifiers by kind again.
  , fn = \ as b -> foldr (\ (P pl (n ::: _T)) b -> case n of
    Just n -> ((pl, n) ::: _T) >~> b
    _      -> _T --> b) b as
  , app = \ f as -> f $$* fmap (unPl_ braces id) as
  , prd = \ as -> case as of
    [] -> parens mempty
    as -> foldl1 (**) as
  , hole = \ n -> annotate Hole $ pretty '?' <> pretty n
  , _Type = annotate Type $ pretty "Type"
  , _Void = annotate Type $ pretty "Void"
  , _Unit = annotate Type $ pretty "Unit"
  , unit = annotate Con $ pretty "Unit"
  , ann' = tm
  , case' = \ s ps -> embed $ pretty "case" <+> setPrec Expr s </> block (commaSep (map (\ (p, b) -> embed (prec Pattern p </> arrow) </> b) ps))
  , wildcard = pretty '_'
  , pcon = \ n ps -> parens (hsep (annotate Con n:toList ps))
  , tuple = tupled
  , decl = ann
  , defn = \ (a :=: b) -> a </> b
  , data' = block . commaSep
  , module_ = \ (n ::: t :=: ds) -> ann (setPrec Var (prettyMName n) ::: fromMaybe (pretty "Module") t) </> block (embed (vsep (intersperse mempty ds)))
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
    TLocal n d -> name P.upper n d
    Local  n d -> name P.lower n d
    Meta     d -> setPrec Var (annotate Hole (pretty '?' <> evar d))
    Cons     n -> setPrec Var (annotate Con (pretty n))
  , tintro = name P.upper
  , intro = name P.lower
  , lam = comp . embed . commaSep
  , clause = \ ns b -> group (align (setPrec Pattern (vsep (map (\ (P pl (n ::: _T)) -> group $ unPl braces id pl (maybe n (ann . (n :::)) _T)) ns)) </> arrow)) </> b
  -- FIXME: group quantifiers by kind again.
  , fn = \ as b -> foldr (\ (P pl (n ::: _T)) b -> case n of
    Just n -> ((pl, n) ::: _T) >~> b
    _      -> _T --> b) b as
  , app = \ f as -> group f $$* fmap (group . unPl_ braces id) as
  , prd = \ as -> case as of
    [] -> parens mempty
    as -> foldl1 (**) as
  , hole = \ n -> annotate Hole $ pretty '?' <> pretty n
  , _Type = annotate Type $ pretty "Type"
  , _Void = annotate Type $ pretty "Void"
  , _Unit = annotate Type $ pretty "Unit"
  , unit = annotate Con $ pretty "Unit"
  , ann' = group . tm
  , case' = \ s ps -> embed $ pretty "case" <+> setPrec Expr s </> block (commaSep (map (\ (p, b) -> embed (prec Pattern p </> arrow) </> b) ps))
  , wildcard = pretty '_'
  , pcon = \ n ps -> parens (hsep (annotate Con n:toList ps))
  , tuple = tupled
  , decl = ann
  , defn = \ (a :=: b) -> a </> b
  , data' = block . commaSep
  , module_ = \ (n ::: t :=: ds) -> ann (setPrec Var (prettyMName n) ::: fromMaybe (pretty "Module") t) </> block (embed (vsep (intersperse mempty ds)))
  }
  where
  embed = nest 2 . group
  name f _ d = setPrec Var (annotate (Name d) (cons d (f (getLevel d))))
