{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Facet.Print
( prettyPrint
, Print(..)
) where

import           Control.Applicative (Const(..), (<**>))
import           Control.Monad.IO.Class
import           Data.Kind (Type)
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Text.Prettyprint.Doc.Render.Terminal as ANSI
import           Facet.Expr
import           Facet.Pretty hiding (Doc, PrecDoc)
import qualified Facet.Pretty as P

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
  deriving (P.Doc (Nest Highlight), Monoid, P.PrecDoc (Nest Highlight), Semigroup, Show)

newtype Print (sig :: Type -> Type) a = Print { runPrint :: Fresh Doc }
  deriving (P.Doc (Nest Highlight), Functor, Monoid, P.PrecDoc (Nest Highlight), Semigroup)
  deriving (Applicative) via Const (Fresh Doc)

data Highlight
  = Name
  | Op
  | Lit
  deriving (Enum, Eq, Ord, Show)

instance Expr Print where
  lam f = Print $ cases [\ var -> (var, runPrint (f (Left (Print var))))]
  f $$ a = Print $ runPrint f <+> runPrint a

  alg _ = Print $ pretty "TBD"

  weakenBy _ = Print . runPrint

cases :: P.Doc ann doc => [Fresh doc -> (Fresh doc, Fresh doc)] -> Fresh doc
cases cs = bind $ \ var -> group
  . encloseSep
    (lbrace <> flatAlt space mempty)
    (flatAlt space mempty <> rbrace)
    (flatAlt (pretty " | ") (pretty "| "))
  $ map (\ (p, b) -> p <+> pretty "->" <+> b) (cs <*> [var])
