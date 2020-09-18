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
, UntypedPrint(..)
, Print(..)
) where

import           Control.Applicative (Const(..), (<**>))
import           Control.Monad.IO.Class
import           Data.Coerce
import qualified Data.Kind as K
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Text.Prettyprint.Doc.Render.Terminal as ANSI
import           Facet.Pretty.Fresh
import           Facet.Pretty.Prec
import           Facet.Pretty.Rainbow
import           Facet.Syntax
import qualified Facet.Syntax.Untyped as U

prettyPrint :: MonadIO m => Print sig a -> m ()
prettyPrint = prettyPrintWith defaultStyle

prettyPrintWith :: MonadIO m => (Nest Highlight -> ANSI.AnsiStyle) -> Print sig a -> m ()
prettyPrintWith style  = putDoc . PP.reAnnotate style . rainbow . runPrec (Level 0) . fresh . runUntypedPrint . runPrint

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

newtype UntypedPrint = UntypedPrint { runUntypedPrint :: Fresh (Prec (Rainbow (PP.Doc (Nest Highlight)))) }
  deriving (Monoid, PrecPrinter (Nest Highlight), Printer (Nest Highlight), Semigroup)

newtype Print (sig :: K.Type -> K.Type) a = Print { runPrint :: UntypedPrint }
  deriving (U.Err, U.Expr, Functor, Monoid, PrecPrinter (Nest Highlight), Printer (Nest Highlight), Semigroup, U.Type)
  deriving (Applicative) via Const UntypedPrint

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


instance Expr Print where
  lam f = Print $ cases [\ var -> (var, coerce (f . Left) var)]
  f $$ a = Print $ runPrint f U.$$ runPrint a

  alg _ = Print $ pretty "TBD"

  weakenBy _ = Print . runPrint

cases :: [UntypedPrint -> (UntypedPrint, UntypedPrint)] -> UntypedPrint
cases cs = UntypedPrint $ bind $ \ var ->
    runUntypedPrint
  . group
  . braces
  . encloseSep
    (flatAlt space mempty)
    (flatAlt space mempty)
    (flatAlt (pretty " , ") (pretty ", "))
  $ map (\ (p, b) -> p <+> arrow <+> b) (cs <*> [prettyVar var])

prettyVar :: Printer (Nest Highlight) doc => Var -> doc
prettyVar (Var i) = name (pretty (alphabet !! r) <> if q > 0 then pretty q else mempty) where
  (q, r) = i `divMod` 26
  alphabet = ['a'..'z']


instance U.Expr UntypedPrint where
  lam0 f = cases [\ var -> (var, f var)]
  lam  f = cases [\ var -> (var, f (Left var))]
  f $$ a = prec (Level 10) f <+> prec (Level 11) a

  -- FIXME: don’t pretty-print local variables with the same name as globals used in the body
  global = pretty

  unit = pretty "()"
  l ** r = tupled [l, r]

instance U.Err UntypedPrint where
  err = pretty "err"

instance U.Type UntypedPrint where
  a --> b = a <+> arrow <+> b
  t >-> f = UntypedPrint $ bind $ \ var -> runUntypedPrint $ let var' = prettyVar var in braces (space <> var' <+> colon <+> t <> space) <+> arrow <+> f var'
  f .$ a = prec (Level 10) f <+> prec (Level 11) a
  l .* r = parens $ l <> comma <+> r
  _Unit = pretty "()"
  _Type = pretty "Type"
  tglobal = pretty
