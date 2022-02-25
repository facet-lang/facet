module Facet.Syntax.Expr.Type
( Type(..)
) where

import           Control.Applicative (liftA2)
import           Facet.Interface
import           Facet.Kind
import           Facet.Name
import           Facet.Quote
import           Facet.Syntax
import qualified Facet.Type.Class as C
import           Facet.Usage

data Type
  = String
  | Var (Var (Either Meta (LName Index)))
  | ForAll Name Kind Type
  | Arrow (Maybe Name) Quantity Type Type
  | Comp (Signature Type) Type
  | App Type Type
  deriving (Eq, Ord, Show)

instance C.Type (Quoter Type) where
  string = pure String
  forAll n k b = ForAll n k <$> binder (\ d' -> Quoter (\ d -> lvar n (toIndexed d d'))) b
  arrow n q = liftA2 (Arrow n q)
  var v = Quoter (\ d -> Var (toIndexed d v))
  ($$) = liftA2 App
  sig |- t = Comp <$> sequenceSignature sig <*> t


lvar :: Name -> Index -> Type
lvar n i = Var (Free (Right (LName i n)))
