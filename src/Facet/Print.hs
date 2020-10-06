{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
, printSurfaceType
, printSurfaceExpr
, printSurfaceClause
, printSurfacePattern
, printSurfaceDecl
, printSurfaceModule
) where

import           Control.Applicative ((<**>))
import           Control.Category ((>>>))
import           Control.Lens (preview)
import           Control.Monad.IO.Class
import           Data.Bifunctor (bimap, first)
import           Data.Foldable (foldl')
import           Data.Text (Text)
import qualified Facet.Core as C
import qualified Facet.Name as N
import qualified Facet.Pretty as P
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
import           Silkscreen.Printer.Prec
import           Silkscreen.Printer.Rainbow
import           Text.Parser.Position

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
  deriving (Monoid, PrecedencePrinter, Printer, Semigroup)

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
  deriving (Eq, Ord, Show)

name :: (PrecedencePrinter p, Ann p ~ Highlight, Level p ~ Context) => (Int -> p) -> N.Name -> p
name s = var . N.prettyNameWith s

op :: (Printer p, Ann p ~ Highlight) => p -> p
op = annotate Op


arrow :: (Printer p, Ann p ~ Highlight) => p
arrow = op (pretty "->")

comp :: Print -> Print
comp
  = group
  . align
  . braces
  . prec Comp
  . enclose space (flatAlt line space)

cases :: [Print] -> Print -> Print
cases vs b = foldr (\ v r -> prec Pattern v <+> r) (arrow <+> group (nest 2 (line' <> prec Expr b))) vs

ann :: Printer p => (p ::: p) -> p
ann (n ::: t) = n </> group (align (colon <+> flatAlt space mempty <> t))

var :: (PrecedencePrinter p, Level p ~ Context, Ann p ~ Highlight) => p -> p
var = setPrec Var . annotate Name

evar :: (PrecedencePrinter p, Level p ~ Context, Ann p ~ Highlight) => Int -> p
evar = var . P.var

tvar :: (PrecedencePrinter p, Level p ~ Context, Ann p ~ Highlight) => Int -> p
tvar = var . P.tvar

prettyMName :: Printer p => N.MName -> p
prettyMName (n N.:. s)  = prettyMName n <> pretty '.' <> pretty s
prettyMName (N.MName s) = pretty s

prettyQName :: PrecedencePrinter p => N.QName -> p
prettyQName (mname N.:.: n) = prettyMName mname <> pretty '.' <> pretty n


instance C.Type Print where
  tglobal = cfree
  tbound = ctbound
  (-->) = (-->)
  (.*) = (**)
  (.$) = ($$)
  _Type = _Type
  _Void = _Void
  _Unit = _Unit
  t >=> b = first (N.prettyNameWith tvar) t >~> b

instance C.Expr Print where
  global = cfree
  bound = cebound
  tlam = lam . braces . ctbound
  lam = lam . cebound
  ($$) = ($$)
  unit = unit
  (**) = (**)

instance C.Module Print Print Print where
  module' n b = ann (var (prettyMName n) ::: pretty "Module") </> braces (vsep b)
  defTerm n (t := b) = ann (var (prettyQName n) ::: t) </> b


printSurfaceType :: ST.Type -> Print
printSurfaceType = go
  where
  go = ST.out >>> \case
    ST.Free n  -> sfree n
    ST.Bound n -> sbound n
    ST.Hole n  -> hole n
    ST.Type    -> _Type
    ST.Void    -> _Void
    ST.Unit    -> _Unit
    t ST.:=> b ->
      let (t', b') = unprefixr (preview ST.forAll_ . dropSpan) b
      in map (first sbound) (t:t') >~~> go b'
    f ST.:$  a ->
      let (f', a') = unprefixl (preview ST.app_ . dropSpan) f
      in go f' $$* fmap go (a' :> a)
    a ST.:-> b -> go a --> go b
    l ST.:*  r -> go l **  go r
    ST.Loc _ t -> go t

sfree :: N.DName -> Print
sfree = var . pretty

cfree :: N.QName -> Print
cfree = var . prettyQName


sbound :: N.Name -> Print
sbound n = var (pretty (N.hint n))

cebound :: N.Name -> Print
cebound = name evar

ctbound :: N.Name -> Print
ctbound = name tvar


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
($$*) = fmap group . foldl' (\ f a -> prec AppL f <> nest 2 (line <> prec AppR a))

(>~>) :: (Print ::: Print) -> Print -> Print
(n ::: t) >~> b = group (align (braces (space <> ann (var n ::: t) <> flatAlt line space))) </> arrow <+> prec FnR b

(>~~>) :: [Print ::: ST.Type] -> Print -> Print
ts >~~> b = foldr go b (groupByType ST.aeq ts)
  where
  go (t, ns) b = (encloseSep mempty mempty (comma <> space) ns ::: printSurfaceType t) >~> b

groupByType :: (t -> t -> Bool) -> [(n ::: t)] -> [(t, [n])]
groupByType eq = \case
  []   -> []
  x:xs -> (ty x, tm x:map tm ys) : groupByType eq zs
    where
    (ys,zs) = span (eq (ty x) . ty) xs


printSurfaceExpr :: SE.Expr -> Print
printSurfaceExpr = go
  where
  go = SE.out >>> \case
    SE.Free n  -> sfree n
    SE.Bound n -> sbound n
    SE.Hole n  -> hole n
    f SE.:$  a ->
      let (f', a') = unprefixl (preview SE.app_ . dropSpan) f
      in go f' $$* fmap go (a' :> a)
    SE.Unit    -> unit
    l SE.:*  r -> go l **  go r
    SE.Comp c  -> printSurfaceComp c
    SE.Loc _ t -> go t

printSurfaceComp :: [SC.Clause SE.Expr] -> Print
printSurfaceComp = comp . concatWith (surround (line' <> comma <> space)) . map printSurfaceClause

printSurfaceClause :: SC.Clause SE.Expr -> Print
printSurfaceClause = SC.out >>> \case
  SC.Clause n b -> prec Pattern (sbound n) <+> case SC.out b of
    SC.Body b   -> arrow <> group (nest 2 (line <> printSurfaceExpr b))
    _           -> printSurfaceClause b
  SC.Body e     -> prec Expr (printSurfaceExpr e)
  SC.Loc _ c    -> printSurfaceClause c

printSurfacePattern :: SP.Pattern N.Name -> Print
printSurfacePattern p = prec Pattern $ case SP.out p of
  SP.Wildcard -> pretty '_'
  SP.Var n    -> sbound n
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


printSurfaceDecl :: SD.Decl -> Print
printSurfaceDecl = go
  where
  go = SD.out >>> \case
    t SD.:=  e -> printSurfaceType t .= printSurfaceExpr e
    t SD.:=> b ->
      let (t', b') = unprefixr (preview SD.forAll_ . dropSpan) b
      in map (first sbound) (t:t') >~~> go b'
    t SD.:-> b -> bimap sbound printSurfaceType t >-> go b
    SD.Loc _ d -> go d

-- FIXME: it would be nice to ensure that this gets wrapped if the : in the same decl got wrapped.
(.=) :: Print -> Print -> Print
t .= b = t </> b

(>->) :: (Print ::: Print) -> Print -> Print
(n ::: t) >-> b = group (align (parens (ann (n ::: t)))) </> arrow <+> prec FnR b


printSurfaceModule :: SM.Module -> Print
printSurfaceModule = SM.fold alg
  where
  alg = \case
    SM.Module  n b -> module' n b
    SM.Def n d -> def (sfree n) (printSurfaceDecl d)
    SM.Loc _ t     -> t


module' :: N.MName -> [Print] -> Print
module' n b = ann (var (prettyMName n) ::: pretty "Module") </> braces (vsep b)

def :: Print -> Print -> Print
def n b = group $ ann (n ::: b)
