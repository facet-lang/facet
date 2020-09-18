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
prettyPrintWith style  = putDoc . PP.reAnnotate style . getDoc . fresh . runPrint

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

getDoc :: Doc -> PP.Doc (Nest Highlight)
getDoc (Doc doc) = rainbow (runPrec (Level 0) doc)

newtype Doc = Doc (Prec (Rainbow (PP.Doc (Nest Highlight))))
  deriving (Monoid, PrecPrinter (Nest Highlight), Printer (Nest Highlight), Semigroup, Show)

newtype UntypedPrint = UntypedPrint { runUntypedPrint :: Fresh Doc }
  deriving (Monoid, PrecPrinter (Nest Highlight), Printer (Nest Highlight), Semigroup)

newtype Print (sig :: K.Type -> K.Type) a = Print { runPrint :: Fresh Doc }
  deriving (Functor, Monoid, PrecPrinter (Nest Highlight), Printer (Nest Highlight), Semigroup)
  deriving (Applicative) via Const (Fresh Doc)

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
  lam f = Print $ cases [\ var -> (var, runPrint (f (Left (Print var))))]
  f $$ a = Print $ runPrint f <+> runPrint a

  alg _ = Print $ pretty "TBD"

  weakenBy _ = Print . runPrint

cases :: Printer (Nest Highlight) doc => [Fresh doc -> (Fresh doc, Fresh doc)] -> Fresh doc
cases cs = bind $ \ var -> group
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


instance U.Expr (Print sig a) where
  lam0 f = Print $ cases [\ var -> (var, runPrint (f (Print var)))]
  lam  f = Print $ cases [\ var -> (var, runPrint (f (Left (Print var))))]
  f $$ a = prec (Level 10) f <+> prec (Level 11) a

  -- FIXME: don’t pretty-print local variables with the same name as globals used in the body
  global = pretty

  unit = pretty "()"
  l ** r = tupled [l, r]

instance U.Err (Print sig a) where
  err = pretty "err"

instance U.Type (Print sig a) where
  a --> b = a <+> arrow <+> b
  t >-> f = Print $ bind $ \ var -> let var' = prettyVar var in braces (space <> var' <+> colon <+> runPrint t <> space) <+> arrow <+> runPrint (f (Print var'))
  f .$ a = prec (Level 10) f <+> prec (Level 11) a
  l .* r = parens $ l <> comma <+> r
  _Unit = pretty "()"
  _Type = pretty "Type"
  tglobal = pretty
