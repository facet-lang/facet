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
, printCoreType
, printCoreQType
, printSurfaceType
, printCoreExpr
, printSurfaceExpr
, printSurfaceClause
, printCorePattern
, printSurfacePattern
, printSurfaceDecl
, printCoreModule
, printSurfaceModule
) where

import           Control.Applicative ((<**>))
import           Control.Category ((>>>))
import           Control.Lens (preview, to)
import           Control.Monad.IO.Class
import           Data.Bifunctor (bimap, first)
import           Data.Foldable (foldl')
import           Data.List (intersperse)
import           Data.Semigroup (stimes)
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Facet.Core.Expr as CE
import qualified Facet.Core.Module as CM
import qualified Facet.Core.Pattern as CP
import qualified Facet.Core.Type as CT
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


printCoreType :: CT.Type -> Print
printCoreType = printCoreQType [] . CT.quote

printCoreQType :: [Print] -> CT.QType -> Print
printCoreQType = go
  where
  go env = \case
    CT.QType    -> _Type
    CT.QVoid    -> _Void
    CT.QUnit    -> _Unit
    t CT.:==> b -> let n' = cbound (tm t) (tvar (length env)) in (n' ::: go env (ty t)) >~> go (n':env) b
    f CT.:$$ as -> foldl' ($$) (either cfree ((env !!) . N.getIndex) f) (fmap (go env) as)
    a CT.:--> b -> go env a --> go env b
    l CT.:**  r -> go env l **  go env r


printSurfaceType :: [Print] -> ST.Type -> Print
printSurfaceType = go
  where
  go env = ST.out >>> \case
    ST.Free n  -> sfree n
    ST.Bound n -> env !! N.getIndex n
    ST.Hole n  -> hole n
    ST.Type    -> _Type
    ST.Void    -> _Void
    ST.Unit    -> _Unit
    t ST.:=> b ->
      let (t', b') = splitr (preview ST.forAll_ . dropSpan) b
      in map (first sbound) (t:t') >~~> go (sbound (tm t):env) b'
    f ST.:$  a ->
      let (f', a') = splitl (preview ST.app_ . dropSpan) f
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

(>~~>) :: [Print ::: ST.Type] -> Print -> Print
ts >~~> b = foldr go b (groupByType ST.aeq ts)
  where
  -- FIXME: this is horribly wrong and probably going to crash
  go (t, ns) b = (commaSep ns ::: printSurfaceType [] t) >~> b

groupByType :: (t -> t -> Bool) -> [(n ::: t)] -> [(t, [n])]
groupByType eq = \case
  []   -> []
  x:xs -> (ty x, tm x:map tm ys) : groupByType eq zs
    where
    (ys,zs) = span (eq (ty x) . ty) xs


printCoreExpr :: CE.Expr -> Print
printCoreExpr = printCoreQExpr [] . CE.quote

printCoreQExpr :: [Print] -> CE.QExpr -> Print
printCoreQExpr = go
  where
  go env = \case
    CE.QFree n   -> cfree n
    CE.QBound n  -> env !! N.getIndex n
    CE.QTLam n b -> let n' = cbound n (tvar (length env)) in lam (braces n') (go (n':env) b)
    CE.QTApp f a -> go env f $$ braces (printCoreQType env a)
    CE.QLam  p b -> lam (printCorePattern ((`cbound` evar (length env)) <$> p)) (go env b)
    f CE.:$$  a  -> go env f $$ go env a
    CE.QUnit     -> unit
    l CE.:**  r  -> go env l **  go env r

printSurfaceExpr :: [Print] -> SE.Expr -> Print
printSurfaceExpr = go
  where
  go env = SE.out >>> \case
    SE.Free n  -> sfree n
    SE.Bound n -> env !! N.getIndex n
    SE.Hole n  -> hole n
    f SE.:$  a ->
      let (f', a') = splitl (preview SE.app_ . dropSpan) f
      in go env f' $$* fmap (go env) (a' :> a)
    SE.Unit    -> unit
    l SE.:*  r -> go env l **  go env r
    SE.Comp c  -> printSurfaceComp env c
    SE.Loc _ t -> go env t

printSurfaceComp :: [Print] -> [SC.Clause SE.Expr] -> Print
printSurfaceComp env = comp . commaSep . map (printSurfaceClause env)

printSurfaceClause :: [Print] -> SC.Clause SE.Expr -> Print
printSurfaceClause env = SC.out >>> \case
  SC.Clause p b -> let { p' = sbound <$> p ; env' = foldr (:) env p' } in printSurfacePattern p' <+> case SC.out b of
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
printSurfacePattern p = prec Pattern $ case SP.out p of
  SP.Wildcard -> pretty '_'
  SP.Var n    -> n
  SP.Tuple p  -> tupled (map printSurfacePattern p)

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
printSurfaceDecl = go []
  where
  go env = SD.out >>> \case
    t SD.:=  e -> printSurfaceType env t .= printSurfaceExpr env e
    t SD.:=> b ->
      let (t', b') = splitr (preview (SD.forAll_.to snd)) b
          ts = map (first sbound) (t:t')
      in ts >~~> go (foldr ((:) . tm) env ts) b'
    t SD.:-> b -> bimap sbound (printSurfaceType env) t >-> go (sbound (tm t):env) b

-- FIXME: it would be nice to ensure that this gets wrapped if the : in the same decl got wrapped.
(.=) :: Print -> Print -> Print
t .= b = t </> b

(>->) :: (Print ::: Print) -> Print -> Print
(n ::: t) >-> b = prec FnR (group (align (parens (ann (n ::: t)))) </> arrow <+> b)


printCoreModule :: CM.Module -> Print
printCoreModule (CM.Module n ds) = ann (var (prettyMName n) ::: pretty "Module") </> block (vsep (map (\ (n, d ::: t) -> ann (cfree n ::: printCoreType t) </> printCoreDef d) ds))

printCoreDef :: CM.Def -> Print
printCoreDef = \case
  CM.DTerm b  -> printCoreExpr b
  CM.DType b  -> printCoreType b
  CM.DData cs -> block (commaSep (map (ann . bimap pretty printCoreType) cs))


printSurfaceModule :: SM.Module -> Print
printSurfaceModule (SM.Module _ n ds) = module' n (map printSurfaceDef ds)

printSurfaceDef :: SM.Def -> Print
printSurfaceDef (SM.Def _ n d) = def (sfree n) (printSurfaceDecl d)


module' :: N.MName -> [Print] -> Print
module' n b = ann (var (prettyMName n) ::: pretty "Module") </> block (vsep (intersperse line b))

def :: Print -> Print -> Print
def n b = group $ ann (n ::: b)
