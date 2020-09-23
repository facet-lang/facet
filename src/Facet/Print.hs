{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
module Facet.Print
( prettyPrint
, prettyPrintWith
, prettyWith
, terminalStyle
, Print(..)
, Context(..)
, TPrint(..)
) where

import           Control.Applicative (Const(..), (<**>))
import           Control.Monad.IO.Class
import           Data.Coerce
import qualified Data.Kind as K
import           Facet.Pretty.Fresh
import           Facet.Pretty.Prec
import           Facet.Pretty.Rainbow
import qualified Facet.Syntax.Typed as T
import qualified Facet.Syntax.Untyped as U
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI

prettyPrint :: MonadIO m => Print -> m ()
prettyPrint = prettyPrintWith terminalStyle

prettyPrintWith :: MonadIO m => (Nest Highlight -> ANSI.AnsiStyle) -> Print -> m ()
prettyPrintWith style = putDoc . prettyWith style

prettyWith :: (Nest Highlight -> a) -> Print -> PP.Doc a
prettyWith style = PP.reAnnotate style . rainbow . runPrec Null . fresh . (`runPrint` const id) . group

terminalStyle :: Nest Highlight -> ANSI.AnsiStyle
terminalStyle = \case
  Nest i   -> colours !! (getNesting i `mod` len)
  Ann Name -> mempty
  Ann Op   -> ANSI.color     ANSI.Cyan
  Ann Lit  -> ANSI.bold
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

type Inner = Fresh (Prec Context (Rainbow (PP.Doc (Nest Highlight))))
type Trans = Context -> Print -> Print

newtype Print = Print { runPrint :: Trans -> Inner }
  deriving (FreshPrinter (Nest Highlight), Monoid, Printer (Nest Highlight), Semigroup)

instance PrecPrinter Context (Nest Highlight) Print where
  askingPrec = coerce (askingPrec :: (Context -> Trans -> Inner) -> Trans -> Inner)
  localPrec f a = Print $ \ t -> localPrec f (askingPrec ((`runPrint` t) . (`t` a)))

withTransition :: Trans -> Print -> Print
withTransition trans a = Print $ \ _ -> runPrint a trans

whenPrec :: PrecPrinter lvl ann p => (lvl -> Bool) -> (p -> p) -> p -> p
whenPrec p f = ifPrec p f id

ifPrec :: PrecPrinter lvl ann p => (lvl -> Bool) -> (p -> p) -> (p -> p) -> p -> p
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
  deriving (U.App, U.Expr, FreshPrinter (Nest Highlight), Functor, U.Global, Monoid, PrecPrinter Context (Nest Highlight), Printer (Nest Highlight), Semigroup, U.Type)
  deriving (Applicative) via Const Print

instance U.ForAll (TPrint sig a) (TPrint sig a) where
  (>=>) = coerce ((U.>=>) :: Print -> (Print -> Print) -> Print)


data Highlight
  = Name
  | Op
  | Lit
  deriving (Enum, Eq, Ord, Show)

name :: Printer (Nest Highlight) doc => doc -> doc
name = annotate (Ann Name)

op :: Printer (Nest Highlight) doc => doc -> doc
op = annotate (Ann Op)


arrow :: Printer (Nest Highlight) doc => doc
arrow = op (pretty "->")


instance T.Expr TPrint where
  lam f = TPrint $ cases [\ var -> (var, coerce (f . Left) var)]
  ($$) = coerce ((U.$$) @Print)

  alg _ = TPrint $ pretty "TBD"

  weakenBy _ = coerce

cases :: [Print -> (Print, Print)] -> Print
cases cs = bind $ \ v -> whenPrec (/= Expr) (prec Expr . withTransition (\case{ Expr -> id ; _ -> (\ b -> arrow <> group (nest 2 (line <> withTransition (const id) b))) }) . group . align . braces . enclose space (flatAlt line space))
  . encloseSep
    mempty
    mempty
    (flatAlt (space <> comma <> space) (comma <> space))
  $ map (\ (a, b) -> withTransition (const id) (prec Pattern a) <+> prec Expr b) (cs <*> [var v])

ann :: Printer ann p => p -> p -> p
ann v t = v </> group (align (colon <+> flatAlt space mempty <> t))

var :: Int -> Print
var = varFrom ['a'..'z']

tvar :: Int -> Print
tvar = varFrom ['A'..'Z']

varFrom :: String -> Int -> Print
varFrom alpha i = setPrec Var (name (pretty (toAlpha alpha i)))

toAlpha :: String -> Int -> String
toAlpha alphabet i = alphabet !! r : if q > 0 then show q else ""
  where
  n = length alphabet
  (q, r) = i `divMod` n


instance U.App Print where
  l $$ r = askingPrec $ \case
    AppL -> op
    _    -> group op
    where
    op = infixl' AppL AppR (\ f a -> f <> nest 2 (line <> a)) l r

instance U.Global Print where
  -- FIXME: don’t shadow globals with locally-bound variables
  global = pretty

instance U.Expr Print where
  -- FIXME: Preserve variable names from user code where possible
  -- FIXME: Use _ in binding positions for unused variables
  lam0 f = cases [\ var -> (var, f var)]
  lam  f = cases [\ var -> (var, f (Left var))]

  unit = pretty "()"
  l ** r = tupled [l, r]

instance U.ForAll Print Print where
  -- FIXME: combine quantification over type variables of the same kind
  t >=> f = bind $ \ v -> let v' = tvar v in group (align (braces (space <> ann v' t <> flatAlt line space))) </> arrow <+> prec FnR (f v')

instance U.Type Print where
  (-->) = infixr' FnL FnR (\ a b -> group (align a) </> arrow <+> b)
  l .* r = parens $ l <> comma <+> r
  _Unit = pretty "()"
  _Type = pretty "Type"


instance U.Module Print Print Print Print where
  n .: b = group $ ann (pretty n) b

instance U.Decl Print Print Print where
  -- FIXME: it would be nice to ensure that this gets wrapped if the : in the same decl got wrapped.
  t .= b = t </> pretty '=' <+> b

  t >-> f = bind $ \ v -> let v' = var v in group (align (parens (ann v' t))) </> arrow <+> prec FnR (f v')
