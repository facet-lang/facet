module Facet.Type.Expr
( Type(..)
) where

import Facet.Interface
import Facet.Kind
import Facet.Name
import Facet.Syntax
import Facet.Type
import Facet.Usage

data Type
  = String
  | Var (Var (Either Meta (LName Index)))
  | ForAll Name Kind Type
  | Arrow (Maybe Name) Quantity Type Type
  | Comp (Signature Type) Type
  | App Type Type
  deriving (Eq, Ord, Show)

-- FIXME: this should be Level -> Type
instance TType (T Type) where
  string = T String
  forAll n (T k) b = T (ForAll n k (getT (b (T (Var (Free (Right (LName (Index 0) n))))))))
  arrow n q (T a) (T b) = T (Arrow n q a b)
  comp sig (T b) = T (Comp (mapSignature getT sig) b)
  app (T f) (T a) = T (App f a)
