{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Print
( prettyPrint
, Print(..)
) where

import           Control.Applicative ((<**>))
import           Control.Monad.IO.Class
import           Data.Kind (Type)
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Text.Prettyprint.Doc.Render.Terminal as ANSI
import           Facet.Expr hiding (var)
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

newtype Print (sig :: Bin (Type -> Type)) a = Print { runPrint :: Fresh Doc }
  deriving (P.Doc (Nest Highlight), Monoid, P.PrecDoc (Nest Highlight), Semigroup)

data Highlight
  = Name
  | Op
  | Lit
  deriving (Enum, Eq, Ord, Show)

instance Expr Print where
  lam f = Print $ cases [\ var -> (var, runPrint (f (Left (Print var))))]
  f $$ a = Print $ runPrint f <+> runPrint a

  unit = annotate (Ann Lit) (pretty "()")

  inlr (Print a) (Print b) = Print $ tupled [a, b]
  exl (Print p) = Print $ pretty "exl" <+> p
  exr (Print p) = Print $ pretty "exr" <+> p

  exlr l r (Print lr) = Print $ pretty "on" <+> lr <+> cases
    [ \ var -> (pretty "InL" <+> var, runPrint (l (Print var)))
    , \ var -> (pretty "InR" <+> var, runPrint (r (Print var)))
    ]
  inl (Print l) = Print $ pretty "InL" <+> l
  inr (Print r) = Print $ pretty "InR" <+> r

  true  = annotate (Ann Lit) (pretty "True")
  false = annotate (Ann Lit) (pretty "False")
  iff c t e = Print $ pretty "if" <+> runPrint c <+> runPrint t <+> runPrint e

  alg _ = Print $ pretty "TBD"

  weaken = Print . runPrint

cases :: P.Doc ann doc => [Fresh doc -> (Fresh doc, Fresh doc)] -> Fresh doc
cases cs = bind $ \ var -> group
  . encloseSep
    (lbrace <> flatAlt space mempty)
    (flatAlt space mempty <> rbrace)
    (flatAlt (pretty " | ") (pretty "| "))
  $ map (\ (p, b) -> p <+> pretty "->" <+> b) (cs <*> [var])
