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
) where

import           Control.Applicative (liftA2, (<**>))
import           Control.Monad ((<=<))
import           Control.Monad.IO.Class
import           Data.Bifunctor (bimap, first)
import           Data.Foldable (foldl')
import           Data.Function (on)
import qualified Data.IntSet as IntSet
import           Data.List (intersperse)
import           Data.List.NonEmpty (NonEmpty)
import           Data.Monoid (First(..))
import           Data.Semigroup (stimes)
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Traversable (mapAccumL)
import qualified Facet.Core.Module as CM
import qualified Facet.Core.Pattern as CP
import qualified Facet.Core.Value as CV
import           Facet.Name hiding (ann)
import qualified Facet.Pretty as P
import           Facet.Stack
import qualified Facet.Surface.Decl as SD
import qualified Facet.Surface.Expr as SE
import qualified Facet.Surface.Module as SM
import qualified Facet.Surface.Pattern as SP
import qualified Facet.Surface.Type as ST
import           Facet.Syntax
import           Prelude hiding ((**))
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import           Silkscreen as P
import           Silkscreen.Printer.Prec hiding (Level)
import qualified Silkscreen.Printer.Prec as P
import           Silkscreen.Printer.Rainbow as P

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
  . enclose space line

commaSep :: [Print] -> Print
commaSep = encloseSep mempty mempty (comma <> space)

ann :: (PrecedencePrinter p, P.Level p ~ Precedence) => (p ::: p) -> p
ann (n ::: t) = prec Ann $ n </> group (align (colon <+> flatAlt space mempty <> t))

var :: (PrecedencePrinter p, P.Level p ~ Precedence) => p -> p
var = setPrec Var

evar :: (PrecedencePrinter p, P.Level p ~ Precedence, Ann p ~ Highlight) => Level -> p
evar = var . annotate . Name <*> P.lower . getLevel

tvar :: (PrecedencePrinter p, P.Level p ~ Precedence, Ann p ~ Highlight) => Level -> p
tvar = var . annotate . Name <*> P.upper . getLevel


prettyMName :: Printer p => MName -> p
prettyMName (n :. s)  = prettyMName n <> pretty '.' <> pretty s
prettyMName (MName s) = pretty s

prettyQName :: PrecedencePrinter p => QName -> p
prettyQName (mname :.: n) = prettyMName mname <> pretty '.' <> pretty n


printCoreValue ::  Level -> CV.Value Print -> Print
printCoreValue = go
  where
  go d = \case
    CV.Type     -> _Type
    CV.Void     -> _Void
    CV.TUnit    -> _Unit
    CV.Unit     -> _Unit
    t CV.:=> b  ->
      let n' = name d
          t' = go d (ty t)
          b' = go (succ d) (b (CV.free n'))
      in if IntSet.member (getLevel d) (getFVs (fvs b')) then
        ((pl (tm t), n') ::: t') >~> bind d b'
      else
        unPl braces id (pl (tm t)) t' --> bind d b'
    CV.Lam n b  ->
      let (vs, (d', b')) = splitr (unLam' (cons <*> var' True)) (d, CV.Lam n b)
          b'' = go d' b'
      in lam (map (\ (d, n) -> var' (IntSet.member (getLevel d) (getFVs (fvs b''))) d n) vs) b''
    -- FIXME: there’s no way of knowing if the quoted variable was a type or expression variable
    -- FIXME: should maybe print the quoted variable differently so it stands out.
    CV.Neut h e -> group $ foldl' (elim d) (CV.unHead (ann . bimap cfree (go d)) id tvar (ann . bimap (annotate Hole . (pretty '?' <>) . evar) (go d)) h) e
    CV.TPrd l r -> go d l ** go d r
    CV.Prd  l r -> go d l ** go d r
  name d = cons d (tvar d)
  clause d (p, b) =
    let (d', p') = mapAccumL (\ d' (_ ::: _T) -> (succ d', ann (evar d' ::: go d _T))) d p
        b' = foldr bind (go d' (b (CV.free <$> p'))) [d..d']
    in nest 2 $ group (prec Pattern (printCorePattern p') </> arrow) </> b'
  elim d f = \case
    CV.App  a -> f $$ go d a
    CV.Case p -> nest 2 $ group $ pretty "case" <+> setPrec Expr f </> block (commaSep (map (clause d) p))

var' :: Bool -> Level -> PlName ::: CV.Value Print -> Print
var' u d (n ::: _T) = group . align $ unPl braces id (pl n) $ ann $ var (annotate (Name d) (p <> unPl tvar evar (pl n) d)) ::: printCoreValue d _T
  where
  p | u         = mempty
    | otherwise = pretty '_'

unLam' :: (Level -> PlName ::: CV.Value a -> a) -> (Level, CV.Value a) -> Maybe ((Level, PlName ::: CV.Value a), (Level, CV.Value a))
unLam' var (d, v) = case CV.unLam v of
  Just (n, t) -> let n' = var d n in Just ((d, n), (succ d, t (CV.free n')))
  Nothing     -> Nothing

lam
  :: [Print] -- ^ the bound variables.
  -> Print   -- ^ the body.
  -> Print
lam vs b = block $ nest 2 $ group (setPrec Pattern (vsep vs) </> arrow) </> b


printContextEntry :: Level -> UName ::: Print -> Print
printContextEntry l (n ::: _T) = ann (cbound n l ::: _T)


printSurfaceType :: (Foldable f, Functor f) => Stack Print -> ST.Type f a -> Print
printSurfaceType = go
  where
  go env = \case
    ST.Free n  -> sfree n
    ST.Bound n -> env ! getIndex n
    ST.Hole n  -> hole n
    ST.Type    -> _Type
    ST.Void    -> _Void
    ST.Unit    -> _Unit
    t ST.:=> b ->
      let (t', b') = splitr (ST.unForAll <=< extract) b
      in forAlls (map (first sbound) (t:t')) (foldMap (go (env:>sbound (tm t))) b')
    f ST.:$  a ->
      let (f', a') = splitl (ST.unApp <=< extract) f
      in foldMap (go env) f' $$* fmap (foldMap (go env)) (a' :> a)
    a ST.:-> b -> foldMap (go env) a --> foldMap (go env) b
    l ST.:*  r -> foldMap (go env) l **  foldMap (go env) r

sfree :: DName -> Print
sfree = var . pretty

cfree :: QName -> Print
cfree = var . prettyQName


sbound :: UName -> Print
sbound = var . pretty

cbound :: UName -> Level -> Print
cbound h level = cons level (h' <> pretty (getLevel level))
  where
  h'
    | T.null (getUName h) = pretty '_'
    | otherwise           = pretty h


hole :: Text -> Print
hole n = annotate Hole $ pretty '?' <> pretty n


_Type, _Void, _Unit :: Print
_Type = annotate Type $ pretty "Type"
_Void = annotate Type $ pretty "Void"
_Unit = annotate Type $ pretty "Unit"

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

($$*) :: Print -> Stack Print -> Print
($$*) = fmap group . foldl' ($$)

(>~>) :: ((Pl, Print) ::: Print) -> Print -> Print
((pl, n) ::: t) >~> b = prec FnR (flatAlt (column (\ i -> nesting (\ j -> stimes (j + 3 - i) space))) mempty <> group (align (unPl braces parens pl (space <> ann (var n ::: t) <> line))) </> arrow <+> b)

forAlls :: (Foldable f, Functor f) => [Print ::: f (ST.Type f a)] -> Print -> Print
forAlls ts b = foldr go b (groupByType ST.aeq ts)
  where
  -- FIXME: this is horribly wrong and probably going to crash
  go (t, ns) b = ((Im, commaSep ns) ::: foldMap (printSurfaceType Nil) t) >~> b

groupByType :: (Foldable f, Functor f) => (t -> t -> Bool) -> [(n ::: f t)] -> [(f t, [n])]
groupByType eq = \case
  []   -> []
  x:xs -> (ty x, tm x:map tm ys) : groupByType eq zs
    where
    (ys,zs) = span (and . liftA2 eq (extract (ty x)) . extract . ty) xs


printSurfaceExpr :: (Foldable f, Functor f) => Stack Print -> SE.Expr f a -> Print
printSurfaceExpr = go
  where
  go env = \case
    SE.Free n  -> sfree n
    SE.Bound n -> env ! getIndex n
    SE.Hole n  -> hole n
    f SE.:$  a ->
      let (f', a') = splitl (SE.unApp <=< extract) f
      in foldMap (go env) f' $$* fmap (foldMap (go env)) (a' :> a)
    SE.Unit    -> unit
    l SE.:*  r -> foldMap (go env) l **  foldMap (go env) r
    SE.Comp c  -> comp . (`foldMap` c) $ \case
      SE.Expr e     -> prec Expr $ foldMap (printSurfaceExpr env) e
      SE.Clauses cs -> commaSep (map (uncurry (printSurfaceClause env)) cs)
      -- comp . commaSep $ map (foldMap (printSurfaceClause env)) c

printSurfaceClause :: (Foldable f, Functor f) => Stack Print -> NonEmpty (f (SP.Pattern f UName)) -> f (SE.Expr f a) -> Print
printSurfaceClause env ps b = foldMap (foldMap printSurfacePattern) ps' <+> arrow <> group (nest 2 (line <> prec Expr (foldMap (printSurfaceExpr env') b)))
  where
  ps' = fmap (fmap sbound) <$> ps
  env' = foldl (foldl (foldl (:>))) env ps'

printCorePattern :: CP.Pattern Print -> Print
printCorePattern = \case
  CP.Wildcard -> pretty '_'
  CP.Var n    -> n
  CP.Tuple p  -> tupled (map printCorePattern p)

printSurfacePattern :: (Foldable f, Functor f) => SP.Pattern f Print -> Print
printSurfacePattern p = prec Pattern $ case p of
  SP.Wildcard -> pretty '_'
  SP.Var n    -> n
  SP.Tuple p  -> tupled (map (foldMap printSurfacePattern) p)

unit :: Print
unit = annotate Con $ pretty "Unit"


printSurfaceDecl :: SD.Decl a -> Print
printSurfaceDecl = go Nil
  where
  go env = \case
    t SD.:=  e -> foldMap (printSurfaceType env) t .= foldMap (printSurfaceExpr env) e
    t SD.:=> b ->
      let (t', b') = splitr (SD.unForAll <=< extract) b
          ts = map (first sbound) (t:t')
      in forAlls ts (foldMap (go (foldl (\ as (a:::_) -> as :> a) env ts)) b')
    t SD.:-> b -> bimap sbound (foldMap (printSurfaceType env)) t >-> foldMap (go (env:>sbound (tm t))) b

extract :: Foldable f => f t -> Maybe t
extract = getFirst . foldMap (First . Just)


-- FIXME: it would be nice to ensure that this gets wrapped if the : in the same decl got wrapped.
(.=) :: Print -> Print -> Print
t .= b = t </> b

(>->) :: (Print ::: Print) -> Print -> Print
(n ::: t) >-> b = prec FnR (group (align (parens (ann (n ::: t)))) </> arrow <+> b)


printCoreModule :: CM.Module Print -> Print
printCoreModule (CM.Module n ds)
  = module' n $ map (\ (n, d ::: t) -> ann (cfree n ::: printCoreValue (Level 0) t) </> printCoreDef d) ds

printCoreDef :: CM.Def Print -> Print
printCoreDef = \case
  CM.DTerm b  -> printCoreValue (Level 0) b
  CM.DType b  -> printCoreValue (Level 0) b
  CM.DData cs -> block . commaSep $ map (ann . fmap (printCoreValue (Level 0)) . first pretty) cs


printSurfaceModule :: SM.Module a -> Print
printSurfaceModule (SM.Module n ds) = module' n (map (foldMap (uncurry printSurfaceDef)) ds)

printSurfaceDef :: Foldable f => DName -> f (SD.Decl a) -> Print
printSurfaceDef n d = def (sfree n) (foldMap printSurfaceDecl d)


module' :: MName -> [Print] -> Print
module' n b = ann (var (prettyMName n) ::: pretty "Module") </> block (vsep (intersperse mempty b))

def :: Print -> Print -> Print
def n b = group $ ann (n ::: b)
