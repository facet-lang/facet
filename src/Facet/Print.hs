{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Print
( prettyPrint
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
import           Facet.Syntax
import qualified Facet.Syntax.Untyped as U
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI

prettyPrint :: MonadIO m => Print -> m ()
prettyPrint = prettyPrintWith defaultStyle

prettyPrintWith :: MonadIO m => (Nest Highlight -> ANSI.AnsiStyle) -> Print -> m ()
prettyPrintWith style  = putDoc . PP.reAnnotate style . rainbow . runPrec Null . fresh . (`runPrint` const id) . group

defaultStyle :: Nest Highlight -> ANSI.AnsiStyle
defaultStyle = \case
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
  | FnL
  | FnR
  | Expr
  | Pattern
  | AppL
  | AppR
  | Var'
  deriving (Bounded, Eq, Ord, Show)

newtype TPrint (sig :: K.Type -> K.Type) a = TPrint { runTPrint :: Print }
  deriving (U.App, U.Err, U.Expr, FreshPrinter (Nest Highlight), Functor, Monoid, PrecPrinter Context (Nest Highlight), Printer (Nest Highlight), Semigroup, U.Type)
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


instance Expr TPrint where
  lam f = TPrint $ cases [\ var -> (var, coerce (f . Left) var)]
  ($$) = coerce app

  alg _ = TPrint $ pretty "TBD"

  weakenBy _ = coerce

cases :: [Print -> (Print, Print)] -> Print
cases cs = bind $ \ var -> whenPrec (/= Expr) (prec Expr . withTransition (\case{ Expr -> id ; _ -> (\ b -> arrow <> group (nest 2 (line <> withTransition (const id) b))) }) . group . align . braces . enclose space (flatAlt line space))
  . encloseSep
    mempty
    mempty
    (flatAlt (space <> comma <> space) (comma <> space))
  $ map (\ (a, b) -> withTransition (const id) (prec Pattern a) <+> prec Expr b) (cs <*> [prettyVar var])

prettyVar :: Var -> Print
prettyVar (Var i) = setPrec Var' (name (pretty (alphabet !! r) <> if q > 0 then pretty q else mempty)) where
  (q, r) = i `divMod` 26
  alphabet = ['a'..'z']


instance U.App Print where
  ($$) = app

instance U.Expr Print where
  lam0 f = cases [\ var -> (var, f var)]
  lam  f = cases [\ var -> (var, f (Left var))]

  -- FIXME: don’t pretty-print local variables with the same name as globals used in the body
  global = pretty

  unit = pretty "()"
  l ** r = tupled [l, r]

instance U.Err Print where
  err = pretty "err"

instance U.ForAll Print Print where
  t >=> f = bind $ \ var -> let var' = prettyVar var in braces (space <> var' <+> colon <+> t <> space) <+> arrow <+> f var'

instance U.Type Print where
  (-->) = infixr' FnL FnR (\ a b -> a <+> arrow <+> b)
  l .* r = parens $ l <> comma <+> r
  _Unit = pretty "()"
  _Type = pretty "Type"
  tglobal = pretty


app :: Print -> Print -> Print
app l r = askingPrec $ \case
  AppL -> op
  _    -> group op
  where
  op = infixl' AppL AppR (\ f a -> f <> nest 2 (line <> a)) l r


instance U.Module Print Print Print Print where
  n .: b = group $ pretty n </> group (colon <+> b)

instance U.Decl Print Print Print where
  t .= b = t </> pretty '=' <+> b

  t >-> f = bind $ \ var -> let var' = prettyVar var in parens (var' <+> colon <+> t) <+> arrow <+> f var'
