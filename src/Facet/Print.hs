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
, prettyPrintWith
, prettyWith
, terminalStyle
, Print(..)
, Context(..)
, TPrint(..)
, evar
, tvar
) where

import           Control.Applicative ((<**>))
import           Control.Monad.IO.Class
import           Data.Coerce
import qualified Data.Kind as K
import qualified Facet.Core as C
import           Facet.Functor.K
import qualified Facet.Name as N
import qualified Facet.Pretty as P
import qualified Facet.Surface as U
import           Facet.Syntax
import qualified Facet.Syntax.Typed as T
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import           Silkscreen.Printer.Fresh
import           Silkscreen.Printer.Prec
import           Silkscreen.Printer.Rainbow

prettyPrint :: MonadIO m => Print -> m ()
prettyPrint = prettyPrintWith terminalStyle

prettyPrintWith :: MonadIO m => (Highlight -> ANSI.AnsiStyle) -> Print -> m ()
prettyPrintWith style = P.putDoc . prettyWith style

prettyWith :: (Highlight -> a) -> Print -> PP.Doc a
prettyWith style = PP.reAnnotate style . runRainbow (annotate . Nest) 0 . runPrec Null . runFresh 0 . (`runPrint` const id) . group

terminalStyle :: Highlight -> ANSI.AnsiStyle
terminalStyle = \case
  Nest i -> colours !! (i `mod` len)
  Name   -> mempty
  Op     -> ANSI.color ANSI.Cyan
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

newtype Print = Print { runPrint :: (Context -> Print -> Print) -> Fresh (Prec Context (Rainbow (PP.Doc Highlight))) }
  deriving (FreshPrinter, Monoid, Printer, Semigroup)

instance PrecedencePrinter Print where
  type Level Print = Context
  askingPrec = coerce (askingPrec :: (Context -> (Context -> Print -> Print) -> Fresh (Prec Context (Rainbow (PP.Doc Highlight)))) -> (Context -> Print -> Print) -> Fresh (Prec Context (Rainbow (PP.Doc Highlight))))
  localPrec f a = Print $ \ t -> localPrec f (askingPrec ((`runPrint` t) . (`t` a)))

instance Show Print where
  showsPrec p = showsPrec p . prettyWith terminalStyle

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

newtype TPrint (sig :: K.Type -> K.Type) a = TPrint { runTPrint :: Print }
  deriving (U.Expr, FreshPrinter, Functor, U.Located, Monoid, PrecedencePrinter, Printer, Semigroup, C.Type, U.Type)
  deriving (Applicative) via K Print


data Highlight
  = Nest Int
  | Name
  | Op
  | Lit
  deriving (Eq, Ord, Show)

name :: (Printer p, Ann p ~ Highlight) => p -> p
name = annotate Name

op :: (Printer p, Ann p ~ Highlight) => p -> p
op = annotate Op


arrow :: (Printer p, Ann p ~ Highlight) => p
arrow = op (pretty "->")


instance T.Expr TPrint where
  lam f = TPrint $ bind $ \ v -> cases (evar v) [\ var -> (var, coerce (f . Left) var)]
  ($$) = coerce app

  alg _ = TPrint $ pretty "TBD"

  weakenBy _ = coerce


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
var = setPrec Var . name

evar :: (PrecedencePrinter p, Level p ~ Context, Ann p ~ Highlight) => Int -> p
evar = var . P.var

tvar :: (PrecedencePrinter p, Level p ~ Context, Ann p ~ Highlight) => Int -> p
tvar = var . P.tvar

instance U.Located Print where
  locate _ = id

instance U.Expr Print where
  -- FIXME: don’t shadow globals with locally-bound variables
  global = pretty
  -- FIXME: Preserve variable names from user code where possible
  -- FIXME: Use _ in binding positions for unused variables
  lam0 n f = cases (name (pretty n)) [\ var -> (var, f var)]
  lam  n f = cases (name (pretty n)) [\ var -> (var, f (Left var))]
  ($$) = app

  unit = pretty "()"
  l ** r = tupled [l, r]

instance U.Type Print where
    -- FIXME: don’t shadow globals with locally-bound variables
  tglobal = pretty
  -- FIXME: combine quantification over type variables of the same kind
  (n ::: t) >~> b = let v' = var (pretty n) in group (align (braces (space <> ann (v' ::: t) <> flatAlt line space))) </> arrow <+> prec FnR (b v')
  (-->) = rightAssoc FnR FnL (\ a b -> group (align a) </> arrow <+> b)
  l .* r = parens $ l <> comma <+> r
  (.$) = app
  _Unit = pretty "()"
  _Type = pretty "Type"

instance C.Type Print where
  tglobal = pretty
  tbound = setPrec Var . name . N.prettyNameWith tvar
  (-->) = (U.-->)
  (.*) = (U..*)
  (.$) = app
  _Unit = U._Unit
  _Type = U._Type
  -- FIXME: combine quantification over type variables of the same kind
  (v ::: t) ==> b = group (align (braces (space <> ann (N.prettyNameWith tvar v ::: t) <> flatAlt line space))) </> arrow <+> prec FnR b


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
