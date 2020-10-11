{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Print
( prettyPrint
, getPrint
, terminalStyle
, Print(..)
, Context(..)
, evar
, tvar
  -- * Interpreters
, printCoreValue
, printCoreValue'
, printSurfaceType
, printSurfaceExpr
, printSurfaceClause
, printCorePattern
, printSurfacePattern
, printSurfaceDecl
, printCoreModule
, printSurfaceModule
) where

import           Control.Applicative ((<**>))
import           Control.Monad.IO.Class
import           Data.Bifunctor (bimap, first)
import           Data.Foldable (foldl')
import           Data.List (intersperse)
import           Data.Maybe (fromMaybe)
import           Data.Semigroup (stimes)
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Facet.Core.Module as CM
import qualified Facet.Core.Pattern as CP
import qualified Facet.Core.Value as CV
import qualified Facet.Name as N
import qualified Facet.Pretty as P
import           Facet.Stack
import qualified Facet.Surface.Comp as SC
import qualified Facet.Surface.Decl as SD
import qualified Facet.Surface.Expr as SE
import qualified Facet.Surface.Module as SM
import qualified Facet.Surface.Pattern as SP
import qualified Facet.Surface.Type as ST
import           Facet.Syntax
import           Prelude hiding ((**))
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import qualified Silkscreen as P
import           Silkscreen.Printer.Prec hiding (Printer)
import           Silkscreen.Printer.Rainbow hiding (Printer)

prettyPrint :: MonadIO m => Print -> m ()
prettyPrint = P.putDoc . getPrint

getPrint :: Print -> PP.Doc ANSI.AnsiStyle
getPrint = PP.reAnnotate terminalStyle . getPrint'

getPrint' :: Print -> PP.Doc Highlight
getPrint' = runRainbow (annotate . Nest) 0 . runPrec Null . runPrint . group

terminalStyle :: Highlight -> ANSI.AnsiStyle
terminalStyle = \case
  Nest i -> colours !! (i `mod` len)
  Name   -> mempty
  Op     -> ANSI.color ANSI.Cyan
  Type   -> ANSI.color ANSI.Yellow
  Con    -> ANSI.color ANSI.Red
  Lit    -> ANSI.bold
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


newtype Print = Print { runPrint :: Prec Context (Rainbow (PP.Doc Highlight)) }
  deriving (Monoid, PrecedencePrinter, P.Printer, Semigroup)

instance Show Print where
  showsPrec p = showsPrec p . getPrint


data Context
  = Null
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
  | Name
  | Con
  | Type
  | Op
  | Lit
  | ANSI ANSI.AnsiStyle
  deriving (Eq, Ord, Show)

op :: (P.Printer p, Ann p ~ Highlight) => p -> p
op = annotate Op


arrow :: (P.Printer p, Ann p ~ Highlight) => p
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

cases :: [Print] -> Print -> Print
cases vs b = foldr (\ v r -> prec Pattern v <+> r) (arrow <+> group (nest 2 (line' <> prec Expr b))) vs

ann :: P.Printer p => (p ::: p) -> p
ann (n ::: t) = n </> group (align (colon <+> flatAlt space mempty <> t))

var :: (PrecedencePrinter p, Level p ~ Context, Ann p ~ Highlight) => p -> p
var = setPrec Var . annotate Name

evar :: (PrecedencePrinter p, Level p ~ Context, Ann p ~ Highlight) => Int -> p
evar = var . P.evar

tvar :: (PrecedencePrinter p, Level p ~ Context, Ann p ~ Highlight) => Int -> p
tvar = var . P.tvar


prettyMName :: P.Printer p => N.MName -> p
prettyMName (n N.:. s)  = prettyMName n <> pretty '.' <> pretty s
prettyMName (N.MName s) = pretty s

prettyQName :: PrecedencePrinter p => N.QName -> p
prettyQName (mname N.:.: n) = prettyMName mname <> pretty '.' <> pretty n


printCoreValue :: Monad m => CV.Value m Print -> m Print
printCoreValue = go (N.Level 0)
  where
  go d = \case
    CV.Type     -> pure _Type
    CV.Void     -> pure _Void
    CV.UnitT    -> pure _Unit
    CV.Unit     -> pure _Unit
    t CV.:=> b  -> do
      let n' = name (tm t)
      t' <- go d (ty t)
      b' <- go (N.incrLevel d) =<< b (CV.bound n')
      pure $ (n' ::: t') >~> b'
    CV.TLam n b -> let n' = name n in lam (braces n') <$> (go (N.incrLevel d) =<< b (CV.bound n'))
    CV.Lam  n b -> let n' = name n in lam         n'  <$> (go (N.incrLevel d) =<< b (CV.bound n'))
    f CV.:$ as  -> (either cfree id f $$*) <$> traverse (go d) as
    a CV.:-> b  -> (-->) <$> go d a <*> go d b
    CV.TPrd l r -> (**)  <$> go d l <*> go d r
    CV.Prd  l r -> (**)  <$> go d l <*> go d r
    where
    name n = cbound n (tvar (N.getLevel d))

printCoreValue' :: Monad m => Stack Print -> CV.Value m N.Level -> m Print
printCoreValue' = go
  where
  go env = \case
    CV.Type     -> pure _Type
    CV.Void     -> pure _Void
    CV.UnitT    -> pure _Unit
    CV.Unit     -> pure _Unit
    t CV.:=> b  -> do
      let n' = name (tm t)
      t' <- go env (ty t)
      b' <- go (env:>n') =<< b (CV.bound d)
      pure $ (n' ::: t') >~> b'
    CV.TLam n b -> let n' = name n in lam (braces n') <$> (go (env:>n') =<< b (CV.bound d))
    CV.Lam  n b -> let n' = name n in lam         n'  <$> (go (env:>n') =<< b (CV.bound d))
    f CV.:$ as  -> (either cfree (fromMaybe (pretty "??") . (env !?) . N.getIndex . N.levelToIndex d) f $$*) <$> traverse (go env) as
    a CV.:-> b  -> (-->) <$> go env a <*> go env b
    CV.TPrd l r -> (**)  <$> go env l <*> go env r
    CV.Prd  l r -> (**)  <$> go env l <*> go env r
    where
    d = N.Level (length env)
    name n = cbound n (tvar (N.getLevel d))


printSurfaceType :: Stack Print -> ST.Type a -> Print
printSurfaceType = go
  where
  go env = \case
    ST.Free n  -> sfree n
    ST.Bound n -> env ! N.getIndex n
    ST.Hole n  -> hole n
    ST.Type    -> _Type
    ST.Void    -> _Void
    ST.Unit    -> _Unit
    t ST.:=> b ->
      let (t', b') = splitr ST.unForAll b
      in forAlls (map (first sbound) (t:t')) (go (env:>sbound (tm t)) b')
    f ST.:$  a ->
      let (f', a') = splitl ST.unApp f
      in go env f' $$* fmap (go env) (a' :> a)
    a ST.:-> b -> go env a --> go env b
    l ST.:*  r -> go env l **  go env r
    ST.Loc _ t -> go env t

sfree :: N.DName -> Print
sfree = var . pretty

cfree :: N.QName -> Print
cfree = var . prettyQName


sbound :: N.UName -> Print
sbound = var . pretty

cbound :: N.UName -> Print -> Print
cbound h id'
  | T.null (N.getUName h) = id'
  | otherwise             = pretty h <> id'


hole :: Text -> Print
hole n = pretty '?' <> pretty n


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

(-->) = rightAssoc FnR FnL (\ a b -> group (align a) </> arrow <+> b)

-- FIXME: left-flatten products
l ** r = tupled [l, r]

($$*) :: Print -> Stack Print -> Print
($$*) = fmap group . foldl' ($$)

(>~>) :: (Print ::: Print) -> Print -> Print
(n ::: t) >~> b = prec FnR (flatAlt (column (\ i -> nesting (\ j -> stimes (j + 3 - i) space))) mempty <> group (align (braces (space <> ann (var n ::: t) <> line))) </> arrow <+> b)

forAlls :: [Print ::: ST.Type a] -> Print -> Print
forAlls ts b = foldr go b (groupByType ST.aeq ts)
  where
  -- FIXME: this is horribly wrong and probably going to crash
  go (t, ns) b = (commaSep ns ::: printSurfaceType Nil t) >~> b

groupByType :: (t -> t -> Bool) -> [(n ::: t)] -> [(t, [n])]
groupByType eq = \case
  []   -> []
  x:xs -> (ty x, tm x:map tm ys) : groupByType eq zs
    where
    (ys,zs) = span (eq (ty x) . ty) xs


printSurfaceExpr :: Stack Print -> SE.Expr a -> Print
printSurfaceExpr = go
  where
  go env = \case
    SE.Free n  -> sfree n
    SE.Bound n -> env ! N.getIndex n
    SE.Hole n  -> hole n
    f SE.:$  a ->
      let (f', a') = splitl SE.unApp f
      in go env f' $$* fmap (go env) (a' :> a)
    SE.Unit    -> unit
    l SE.:*  r -> go env l **  go env r
    SE.Comp c  -> printSurfaceComp env c
    SE.Loc _ t -> go env t

printSurfaceComp :: Stack Print -> [SC.Clause SE.Expr a] -> Print
printSurfaceComp env = comp . commaSep . map (printSurfaceClause env)

printSurfaceClause :: Stack Print -> SC.Clause SE.Expr a -> Print
printSurfaceClause env = \case
  SC.Clause p b -> let { p' = sbound <$> p ; env' = foldl (:>) env p' } in printSurfacePattern p' <+> case b of
    SC.Body b -> arrow <> group (nest 2 (line <> printSurfaceExpr env' b))
    _         -> printSurfaceClause env' b
  SC.Body e     -> prec Expr (printSurfaceExpr env e)
  SC.Loc _ c    -> printSurfaceClause env c

printCorePattern :: CP.Pattern Print -> Print
printCorePattern = prec Pattern . \case
  CP.Wildcard -> pretty '_'
  CP.Var n    -> n
  CP.Tuple p  -> tupled (map printCorePattern p)

printSurfacePattern :: SP.Pattern Print -> Print
printSurfacePattern p = prec Pattern $ case p of
  SP.Wildcard -> pretty '_'
  SP.Var n    -> n
  SP.Tuple p  -> tupled (map printSurfacePattern p)
  SP.Loc _ p  -> printSurfacePattern p

-- FIXME: Use _ in binding positions for unused variables
lam :: Print -> Print -> Print
lam n = lams [n]

lams :: [Print] -> Print -> Print
lams ns b = askingPrec $ \case
  Comp -> cases ns b
  _    -> comp (cases ns b)

unit :: Print
unit = annotate Con $ pretty "Unit"


printSurfaceDecl :: SD.Decl a -> Print
printSurfaceDecl = go Nil
  where
  go env = \case
    t SD.:=  e -> printSurfaceType env t .= printSurfaceExpr env e
    t SD.:=> b ->
      let (t', b') = splitr SD.unForAll b
          ts = map (first sbound) (t:t')
      in forAlls ts (go (foldl (\ as (a:::_) -> as :> a) env ts) b')
    t SD.:-> b -> bimap sbound (printSurfaceType env) t >-> go (env:>sbound (tm t)) b
    SD.Loc _ d -> go env d

-- FIXME: it would be nice to ensure that this gets wrapped if the : in the same decl got wrapped.
(.=) :: Print -> Print -> Print
t .= b = t </> b

(>->) :: (Print ::: Print) -> Print -> Print
(n ::: t) >-> b = prec FnR (group (align (parens (ann (n ::: t)))) </> arrow <+> b)


printCoreModule :: Monad m => CM.Module m -> m Print
printCoreModule (CM.Module n ds)
  = module' n <$> traverse (\ (n, d ::: t) -> (</>) . ann . (cfree n :::) <$> printCoreValue' Nil t <*> printCoreDef d) ds

printCoreDef :: Monad m => CM.Def m -> m Print
printCoreDef = \case
  CM.DTerm b  -> printCoreValue' Nil b
  CM.DType b  -> printCoreValue' Nil b
  CM.DData cs -> block . commaSep <$> traverse (fmap ann . traverse (printCoreValue' Nil) . first pretty) cs


printSurfaceModule :: SM.Module a -> Print
printSurfaceModule (SM.Module _ n ds) = module' n (map printSurfaceDef ds)

printSurfaceDef :: SM.Def a -> Print
printSurfaceDef (SM.Def _ n d) = def (sfree n) (printSurfaceDecl d)


module' :: N.MName -> [Print] -> Print
module' n b = ann (var (prettyMName n) ::: pretty "Module") </> block (vsep (intersperse line b))

def :: Print -> Print -> Print
def n b = group $ ann (n ::: b)
