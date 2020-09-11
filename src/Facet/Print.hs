{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
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
import           Facet.Expr
import           Facet.Pretty hiding (Doc, PrecDoc)
import qualified Facet.Pretty as P

prettyPrint :: MonadIO m => Print sig a -> m ()
prettyPrint = prettyPrintWith defaultStyle

prettyPrintWith :: MonadIO m => (Highlight Nesting -> ANSI.AnsiStyle) -> Print sig a -> m ()
prettyPrintWith style  = putDoc . PP.reAnnotate style . getDoc . runPrint

defaultStyle :: Highlight Nesting -> ANSI.AnsiStyle
defaultStyle = \case
  Name     -> mempty
  Op       -> ANSI.color     ANSI.Cyan
  Lit      -> ANSI.bold
  Nest i   -> colours !! (getNesting i `mod` len)
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

getDoc :: Doc -> PP.Doc (Highlight Nesting)
getDoc (Doc doc) = rainbow (runPrec (Level 0) doc)

newtype Doc = Doc (Prec (Rainbow (PP.Doc (Highlight Nesting))))
  deriving (P.Doc (Highlight Nesting), Monoid, P.PrecDoc (Highlight Nesting), Semigroup, Show)

newtype Print (sig :: Bin (Type -> Type)) a = Print { runPrint :: Doc }
  deriving (P.Doc (Highlight Nesting), Monoid, P.PrecDoc (Highlight Nesting), Semigroup)

data Highlight a
  = Name
  | Op
  | Lit
  | Nest a
  deriving (Functor)

instance Applicative Highlight where
  pure = Nest
  f <*> a = case f of
      Name     -> Name
      Op       -> Op
      Lit      -> Lit
      Nest f   -> f <$> a
