module Facet.Type.Expr
( Type(..)
) where

import           Control.Applicative (liftA2)
import           Facet.Interface
import           Facet.Kind
import           Facet.Name
import           Facet.Quote
import           Facet.Syntax
import           Facet.Type
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
  forAll n k b = ForAll n k <$> binder (\ d d' -> lvar n (toIndexed d' d)) b
  arrow n q = liftA2 (Arrow n q)
  var v = Quoter (\ d -> Var (toIndexed d v))
  ($$) = liftA2 App
  sig |- t = Comp <$> sequenceSignature sig <*> t

-- FIXME: this should be Level -> Type
instance TType (T (Level -> Type)) where
  string = T (const String)
  forAll n (T k) b = T (\ d -> ForAll n k (getT (b (T (lvar n . toIndexed d))) d))
  arrow n q (T a) (T b) = T (\ d -> Arrow n q (a d) (b d))
  comp sig (T b) = T (\ d -> Comp (mapSignature (\ (T i) -> i d) sig) (b d))
  app (T f) (T a) = T (\ d -> App (f d) (a d))


lvar :: Name -> Index -> Type
lvar n i = Var (Free (Right (LName i n)))
