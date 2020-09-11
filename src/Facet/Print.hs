{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
module Facet.Print
( Print(..)
) where

import           Data.Kind (Type)
import qualified Data.Text.Prettyprint.Doc as PP
import           Facet.Expr
import           Facet.Pretty hiding (Doc, PrecDoc)
import qualified Facet.Pretty as P

newtype Doc = Doc (Prec (Rainbow (PP.Doc (Highlight Int))))
  deriving (P.Doc (Highlight Int), Monoid, P.PrecDoc (Highlight Int), Semigroup, Show)

newtype Print (sig :: Bin (Type -> Type)) a = Print { print :: Doc }
  deriving (P.Doc (Highlight Int), Monoid, P.PrecDoc (Highlight Int), Semigroup)

newtype Highlight a = Highlight a
  deriving (Functor)

instance Applicative Highlight where
  pure = Highlight
  Highlight f <*> Highlight a = Highlight (f a)
