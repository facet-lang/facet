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
getPrint' = doc . runRainbow (annotate . Nest) 0 . runPrec Null . ($ (Level 0)) . runPrint . group

terminalStyle :: Highlight -> ANSI.AnsiStyle
terminalStyle = \case
  Nest i -> colours !! (i `mod` len)
  Name i -> reverse colours !! (i `mod` len)
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


data Doc = Doc
  { fvs :: FVs
  , doc :: PP.Doc Highlight
  }

instance Semigroup Doc where
  Doc v1 d1 <> Doc v2 d2 = Doc (v1 <> v2) (d1 <> d2)
  stimes n (Doc v d) = Doc (stimes n v) (stimes n d)

instance Monoid Doc where
  mempty = Doc mempty mempty

instance Vars Doc where
  use l = Doc (use l) mempty
  cons l d = Doc (cons l (fvs d)) (doc d)
  bind l d = Doc (bind l (fvs d)) (doc d)

instance Printer Doc where
  type Ann Doc = Highlight

  liftDoc0 a = Doc mempty a
  liftDoc1 f (Doc v d) = Doc v (f d)
  liftDoc2 f (Doc v1 d1) (Doc v2 d2) = Doc (v1 <> v2) (f d1 d2)

  -- NB: column, nesting, & pageWidth all destroy fvs.
  column    f = Doc mempty (column    (doc . f))
  nesting   f = Doc mempty (nesting   (doc . f))
  pageWidth f = Doc mempty (pageWidth (doc . f))

  enclosing (Doc vl dl) (Doc vr dr) (Doc vx dx) = Doc (vl <> vr <> vx) (enclosing dl dr dx)

  brackets (Doc v d) = Doc v (brackets d)
  braces   (Doc v d) = Doc v (braces   d)
  parens   (Doc v d) = Doc v (parens   d)
  angles   (Doc v d) = Doc v (angles   d)
  squotes  (Doc v d) = Doc v (squotes  d)
  dquotes  (Doc v d) = Doc v (dquotes  d)

newtype Print = Print { runPrint :: Level -> Prec Precedence (Rainbow Doc) }
  deriving (Monoid, PrecedencePrinter, Printer, Semigroup)

instance Vars Print where
  use l = Print $ \ _ -> pure (Rainbow (use l))
  cons l (Print b) = Print $ \ d -> Prec $ \ p -> Rainbow $ \ t n -> cons l (runRainbow t n (runPrec p (b d)))
  bind l (Print b) = Print $ \ d -> Prec $ \ p -> Rainbow $ \ t n -> bind l (runRainbow t n (runPrec p (b (succ d))))

instance Show Print where
  showsPrec p = showsPrec p . getPrint

-- FIXME: NO. BAD.
instance Eq Print where
  (==) = (==) `on` show

withLevel :: (Level -> Print) -> Print
withLevel f = Print $ \ d -> runPrint (f d) d

setLevel :: Level -> Print -> Print
setLevel l p = Print $ \ _ -> runPrint p l


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
  | Name Int
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

ann :: Printer p => (p ::: p) -> p
ann (n ::: t) = n </> group (align (colon <+> flatAlt space mempty <> t))

var :: (PrecedencePrinter p, P.Level p ~ Precedence) => p -> p
var = setPrec Var

evar :: (PrecedencePrinter p, P.Level p ~ Precedence, Ann p ~ Highlight) => Int -> p
evar = var . annotate . Name <*> P.evar

tvar :: (PrecedencePrinter p, P.Level p ~ Precedence, Ann p ~ Highlight) => Int -> p
tvar = var . annotate . Name <*> P.tvar


prettyMName :: Printer p => MName -> p
prettyMName (n :. s)  = prettyMName n <> pretty '.' <> pretty s
prettyMName (MName s) = pretty s

prettyQName :: PrecedencePrinter p => QName -> p
prettyQName (mname :.: n) = prettyMName mname <> pretty '.' <> pretty n


printCoreValue ::  CV.Value Print -> Print
printCoreValue = go
  where
  go = \case
    CV.Type     -> _Type
    CV.Void     -> _Void
    CV.TUnit    -> _Unit
    CV.Unit     -> _Unit
    -- FIXME: print as --> when the bound variable is unused
    t CV.:=> b  -> withLevel $ \ d ->
      let n' = name d
          t' = go (ty t)
          b' = bind d (go (b (CV.bound n')))
      in ((pl (tm t), n') ::: t') >~> b'
    CV.Lam n b  -> withLevel $ \ d ->
      let (vs, (_, b')) = splitr unLam' (d, CV.Lam n b)
      in lam (map snd vs) (foldr (bind . fst) (go b') vs)
    -- FIXME: there’s no way of knowing if the quoted variable was a type or expression variable
    -- FIXME: should maybe print the quoted variable differently so it stands out.
    CV.Neut h e -> CV.unHead cfree id (tvar . getLevel) (annotate Hole . (pretty '?' <>) . evar . getLevel) h $$* fmap elim e
    CV.TPrd l r -> go l ** go r
    CV.Prd  l r -> go l ** go r
  name d = cons d (tvar (getLevel d))
  clause (p, b) = withLevel $ \ d ->
    let (d', p') = mapAccumL (\ d _ -> (succ d, let n' = evar (getLevel d) in (n', CV.bound n'))) d p
        b' = foldr bind (go (b (snd <$> p'))) [d..d']
    in printCorePattern (fst <$> p') <+> arrow <+> b'
  elim = \case
    CV.App  a -> go a
    CV.Case p -> (pretty "case" <>) . block . commaSep $ map clause p

var' :: Level -> PlName -> Print
var' d n = unPl (braces . tvar) evar (pl n) (getLevel d)

unLam' :: (Level, CV.Value Print) -> Maybe ((Level, Print), (Level, CV.Value Print))
unLam' (d, v) = case CV.unLam v of
  Just (n, t) -> let n' = var' d n in Just ((d, n'), (succ d, t (CV.bound (cons d n'))))
  Nothing     -> Nothing

lam
  :: [Print] -- ^ the bound variables.
  -> Print   -- ^ the body.
  -> Print
lam vs b = block $ hsep vs <+> arrow <> nest 2 (line <> b)


printContextEntry :: Level -> UName ::: Print -> Print
printContextEntry l (n ::: _T) = setLevel l $ ann (cbound n l ::: _T)


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
printCorePattern = prec Pattern . \case
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


printSurfaceDecl :: (Foldable f, Functor f) => SD.Decl f a -> Print
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
  = module' n $ map (\ (n, d ::: t) -> ann (cfree n ::: printCoreValue t) </> printCoreDef d) ds

printCoreDef :: CM.Def Print -> Print
printCoreDef = \case
  CM.DTerm b  -> printCoreValue b
  CM.DType b  -> printCoreValue b
  CM.DData cs -> block . commaSep $ map (ann . fmap printCoreValue . first pretty) cs


printSurfaceModule :: (Foldable f, Functor f) => SM.Module f a -> Print
printSurfaceModule (SM.Module n ds) = module' n (map (foldMap (uncurry printSurfaceDef)) ds)

printSurfaceDef :: (Foldable f, Functor f) => DName -> f (SD.Decl f a) -> Print
printSurfaceDef n d = def (sfree n) (foldMap printSurfaceDecl d)


module' :: MName -> [Print] -> Print
module' n b = ann (var (prettyMName n) ::: pretty "Module") </> block (vsep (intersperse mempty b))

def :: Print -> Print -> Print
def n b = group $ ann (n ::: b)
