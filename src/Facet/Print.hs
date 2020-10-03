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
) where

import           Control.Applicative ((<**>))
import           Control.Monad.IO.Class
import           Data.Bifunctor (first)
import           Data.Coerce
import           Data.Text (Text)
import qualified Facet.Core as C
import qualified Facet.Name as N
import qualified Facet.Pretty as P
import qualified Facet.Surface as S
import qualified Facet.Surface.Type as ST
import           Facet.Syntax
import           Prelude hiding ((**))
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import           Silkscreen.Printer.Prec
import           Silkscreen.Printer.Rainbow

prettyPrint :: MonadIO m => Print -> m ()
prettyPrint = P.putDoc . getPrint

getPrint :: Print -> PP.Doc ANSI.AnsiStyle
getPrint = PP.reAnnotate terminalStyle . getDoc . getPrint'

getPrint' :: Print -> Doc
getPrint' = runRainbow (annotate . Nest) 0 . runPrec Null . (`runPrint` const id) . group

terminalStyle :: Highlight -> ANSI.AnsiStyle
terminalStyle = \case
  Nest i -> colours !! (i `mod` len)
  Name   -> mempty
  Op     -> ANSI.color ANSI.Cyan
  Type   -> ANSI.color ANSI.Yellow
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

data Doc = Doc { fvs :: N.FVs, getDoc :: PP.Doc Highlight }

instance Semigroup Doc where
  Doc m1 d1 <> Doc m2 d2 = Doc (m1 <> m2) (d1 <> d2)

instance Monoid Doc where
  mempty = Doc mempty mempty

instance Printer Doc where
  type Ann Doc = Highlight
  liftDoc0 = Doc mempty
  liftDoc1 f (Doc m d) = Doc m (f d)
  liftDoc2 f (Doc m1 d1) (Doc m2 d2) = Doc (m1 <> m2) (f d1 d2)

newtype Print = Print { runPrint :: (Context -> Print -> Print) -> Prec Context (Rainbow Doc) }
  deriving (Monoid, Printer, Semigroup)

instance PrecedencePrinter Print where
  type Level Print = Context
  askingPrec = coerce (askingPrec :: (Context -> (Context -> Print -> Print) -> Prec Context (Rainbow Doc)) -> (Context -> Print -> Print) -> Prec Context (Rainbow Doc))
  localPrec f a = Print $ \ t -> localPrec f (askingPrec ((`runPrint` t) . (`t` a)))

instance Show Print where
  showsPrec p = showsPrec p . getPrint

instance N.Scoped Print where
  fvs = fvs . getPrint'

withTransition :: (Context -> Print -> Print) -> Print -> Print
withTransition trans a = Print $ \ _ -> runPrint a trans

whenPrec :: PrecedencePrinter p => (Level p -> Bool) -> (p -> p) -> p -> p
whenPrec p f = ifPrec p f id

ifPrec :: PrecedencePrinter p => (Level p -> Bool) -> (p -> p) -> (p -> p) -> p -> p
ifPrec p f g a = askingPrec $ \ p' -> if p p' then f a else g a


data Context
  = Null
  | FnR
  | FnL
  | Expr
  | Pattern
  | AppL
  | AppR
  | Var
  deriving (Bounded, Eq, Ord, Show)

data Highlight
  = Nest Int
  | Name
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


cases :: Print -> [Print] -> Print
cases v cs = whenPrec (/= Expr) (prec Expr . withTransition (\case{ Expr -> id ; _ -> (\ b -> arrow <> group (nest 2 (line <> withTransition (const id) b))) }) . group . align . braces . enclose space (flatAlt line space))
  . encloseSep
    mempty
    mempty
    (flatAlt (space <> comma <> space) (comma <> space))
  $ map (\ b -> withTransition (const id) (prec Pattern v) <+> prec Expr b) cs

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


instance S.Located Print where
  locate _ = id

instance S.Expr Print where
  global = sfree . S.getEName
  bound = sbound
  lam = lam . sbound
  ($$) = ($$)

  unit = pretty "()"
  l ** r = tupled [l, r]

instance S.Type Print where
  tglobal = sfree . S.getTName
  tbound = sbound
  -- FIXME: combine quantification over type variables of the same kind
  (n ::: t) >~> b = group (align (braces (space <> ann (var (pretty (N.hint n)) ::: t) <> flatAlt line space))) </> arrow <+> prec FnR b
  (-->) = rightAssoc FnR FnL (\ a b -> group (align a) </> arrow <+> b)
  l .* r = parens $ l <> comma <+> r
  (.$) = ($$)
  _Unit = pretty "()"
  _Type = annotate Type $ pretty "Type"

instance C.Type Print where
  tglobal = cfree
  tbound = ctbound
  (-->) = (S.-->)
  (.*) = (S..*)
  (.$) = ($$)
  _Unit = S._Unit
  _Type = annotate Type S._Type
  -- FIXME: combine quantification over type variables of the same kind
  (v ::: t) ==> b = group (align (braces (space <> ann (N.prettyNameWith tvar v ::: t) <> flatAlt line space))) </> arrow <+> prec FnR b

instance C.Expr Print where
  global = cfree
  bound = cebound
  tlam = lam . braces . ctbound
  lam = lam . cebound
  ($$) = ($$)
  unit = pretty "()"
  l ** r = tupled [l, r]

instance C.Module Print Print Print where
  module' n b = ann (var (prettyMName n) ::: pretty "Module") </> braces (vsep b)
  defTerm n (t := b) = ann (var (prettyQName n) ::: t) </> b

instance S.Module Print Print Print Print where
  module' n b = ann (var (prettyMName n) ::: pretty "Module") </> braces (vsep b)
  defTerm n b = group $ ann (var (pretty n) ::: b)
  defType n b = group $ ann (var (pretty n) ::: b)

instance S.Decl Print Print Print where
  -- FIXME: it would be nice to ensure that this gets wrapped if the : in the same decl got wrapped.
  t .= b = t </> b

    -- FIXME: combine quantification over type variables of the same kind
  (n ::: t) >=> b = group (align (braces (space <> ann (var (pretty (N.hint n)) ::: t) <> flatAlt line space))) </> arrow <+> prec FnR b

  (n ::: t) >-> b = group (align (parens (ann (var (pretty (N.hint n)) ::: t)))) </> arrow <+> prec FnR b


printSurfaceType :: ST.Type -> Print
printSurfaceType = ST.fold alg
  where
  alg = \case
    ST.Free n  -> sfree (S.getTName n)
    ST.Bound n -> sbound n
    ST.Type    -> _Type
    ST.Unit    -> _Unit
    t ST.:=> b -> first (var . pretty . N.hint) t >~> b
    f ST.:$  a -> f $$  a
    a ST.:-> b -> a --> b
    l ST.:*  r -> l **  r
    ST.Ann _ t -> t

sfree :: Text -> Print
sfree = var . pretty

cfree :: N.QName -> Print
cfree = var . prettyQName


sbound :: N.Name -> Print
sbound n = var (pretty (N.hint n))

cebound :: N.Name -> Print
cebound = name evar

ctbound :: N.Name -> Print
ctbound = name tvar

_Unit, _Type :: Print
_Unit = annotate Type $ pretty "Unit"
_Type = annotate Type $ pretty "Type"

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

(>~>) :: (Print ::: Print) -> Print -> Print
-- FIXME: combine quantification over type variables of the same kind
(n ::: t) >~> b = group (align (braces (space <> ann (var n ::: t) <> flatAlt line space))) </> arrow <+> prec FnR b


-- FIXME: Use _ in binding positions for unused variables
lam :: Print -> Print -> Print
lam n b = cases n [b]
