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
) where

import           Control.Applicative ((<**>))
import           Control.Monad.IO.Class
import           Data.Coerce
import qualified Facet.Core as C
import qualified Facet.Name as N
import qualified Facet.Pretty as P
import qualified Facet.Surface as U
import           Facet.Syntax
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import           Silkscreen.Printer.Fresh
import           Silkscreen.Printer.Prec
import           Silkscreen.Printer.Rainbow

prettyPrint :: MonadIO m => Print -> m ()
prettyPrint = P.putDoc . getPrint

getPrint :: Print -> PP.Doc ANSI.AnsiStyle
getPrint = PP.reAnnotate terminalStyle . getDoc . getPrint'

getPrint' :: Print -> Doc
getPrint' = runRainbow (annotate . Nest) 0 . runPrec Null . runFresh 0 . (`runPrint` const id) . group

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

newtype Print = Print { runPrint :: (Context -> Print -> Print) -> Fresh (Prec Context (Rainbow Doc)) }
  deriving (FreshPrinter, Monoid, Printer, Semigroup)

instance PrecedencePrinter Print where
  type Level Print = Context
  askingPrec = coerce (askingPrec :: (Context -> (Context -> Print -> Print) -> Fresh (Prec Context (Rainbow Doc))) -> (Context -> Print -> Print) -> Fresh (Prec Context (Rainbow Doc)))
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


cases :: Print -> [Print -> (Print, Print)] -> Print
cases v cs = whenPrec (/= Expr) (prec Expr . withTransition (\case{ Expr -> id ; _ -> (\ b -> arrow <> group (nest 2 (line <> withTransition (const id) b))) }) . group . align . braces . enclose space (flatAlt line space))
  . encloseSep
    mempty
    mempty
    (flatAlt (space <> comma <> space) (comma <> space))
  $ map (\ (a, b) -> withTransition (const id) (prec Pattern a) <+> prec Expr b) (cs <*> [v])

ann :: Printer p => (p ::: p) -> p
ann (n ::: t) = n </> group (align (colon <+> flatAlt space mempty <> t))

var :: (PrecedencePrinter p, Level p ~ Context, Ann p ~ Highlight) => p -> p
var = setPrec Var . annotate Name

evar :: (PrecedencePrinter p, Level p ~ Context, Ann p ~ Highlight) => Int -> p
evar = var . P.var

tvar :: (PrecedencePrinter p, Level p ~ Context, Ann p ~ Highlight) => Int -> p
tvar = var . P.tvar

instance U.Located Print where
  locate _ = id

instance U.Expr Print where
  global = pretty
  -- FIXME: Use _ in binding positions for unused variables
  lam0 n f = cases (annotate Name (pretty n)) [\ var -> (var, f var)]
  lam  n f = cases (annotate Name (pretty n)) [\ var -> (var, f (Left var))]
  ($$) = app

  unit = pretty "()"
  l ** r = tupled [l, r]

instance U.Type Print where
  tglobal = pretty
  -- FIXME: combine quantification over type variables of the same kind
  (n ::: t) >~> b = let v' = var (pretty n) in group (align (braces (space <> ann (v' ::: t) <> flatAlt line space))) </> arrow <+> prec FnR (b v')
  (-->) = rightAssoc FnR FnL (\ a b -> group (align a) </> arrow <+> b)
  l .* r = parens $ l <> comma <+> r
  (.$) = app
  _Unit = pretty "()"
  _Type = annotate Type $ pretty "Type"

instance C.Type Print where
  tglobal = pretty
  tbound = name tvar
  (-->) = (U.-->)
  (.*) = (U..*)
  (.$) = app
  _Unit = U._Unit
  _Type = annotate Type U._Type
  -- FIXME: combine quantification over type variables of the same kind
  (v ::: t) ==> b = group (align (braces (space <> ann (N.prettyNameWith tvar v ::: t) <> flatAlt line space))) </> arrow <+> prec FnR b

instance C.Expr Print where
  global = pretty
  bound = name evar
  tlam n b = cases (braces (C.bound n)) [\ v -> (v, b)]
  lam0 n b = cases (C.bound n) [\ v -> (v, b)]
  ($$) = app

instance C.Module Print Print Print where
  module' n b = ann (pretty n ::: pretty "Module") </> braces b
  n .:. t := b = ann (pretty n ::: t) </> braces b

instance U.Module Print Print Print Print where
  n .:. b = group $ ann (pretty n ::: b)

instance U.Decl Print Print Print where
  -- FIXME: it would be nice to ensure that this gets wrapped if the : in the same decl got wrapped.
  -- FIXME: we don’t parse =, we shouldn’t print it here.
  t .= b = t </> pretty '=' <+> b

    -- FIXME: combine quantification over type variables of the same kind
  (n ::: t) >=> b = let v' = var (pretty n) in group (align (braces (space <> ann (v' ::: t) <> flatAlt line space))) </> arrow <+> prec FnR (b v')

  (n ::: t) >-> f = let v' = var (pretty n) in group (align (parens (ann (v' ::: t)))) </> arrow <+> prec FnR (f v')

app :: Print -> Print -> Print
l `app` r = askingPrec $ \case
  AppL -> op
  _    -> group op
  where
  -- FIXME: lambdas get parenthesized on the left
  op = leftAssoc AppL AppR (\ f a -> f <> nest 2 (line <> a)) l r
