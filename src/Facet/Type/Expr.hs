module Facet.Type.Expr
( Type(..)
) where

import           Control.Applicative (liftA2)
import           Facet.Interface
import           Facet.Kind
import           Facet.Name
import           Facet.Quote
import           Facet.Syntax
import qualified Facet.Type.Class as C

data Type
  = String
  | Var (Var (Either Meta Index))
  | ForAll Name Kind Type
  | Arrow (Maybe Name) Type Type
  | Comp (Signature Type) Type
  | App Type Type
  deriving (Eq, Ord, Show)

instance C.Type (Quoter Type) where
  string = pure String
  forAll n k b = ForAll n k <$> binder (\ d' -> Quoter (\ d -> Var (Free (Right (toIndexed d d'))))) b
  arrow n = liftA2 (Arrow n)
  var v = Quoter (\ d -> Var (toIndexed d v))
  ($$) = liftA2 App
  sig |- t = Comp <$> sequenceSignature sig <*> t
