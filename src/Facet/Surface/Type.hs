{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Type
( TName(..)
, Type(..)
, global_
, bound_
, hole_
, _ForAll
, _Arrow
, _App
, _Prd
, _Unit
, _Type
, dropAnn
, aeq
, TypeF(..)
, fold
) where

import Control.Lens.Prism
import Data.String (IsString(..))
import Data.Text (Text)
import Facet.Name
import Facet.Syntax
import Prettyprinter (Pretty)
import Text.Parser.Position (Located(..), Span)

newtype TName = TName { getTName :: Text }
  deriving (Eq, IsString, Ord, Pretty, Show)

newtype Type = In { out :: TypeF Type }

instance Located Type where
  locate = fmap In . Ann

global_ :: Prism' Type TName
global_ = prism' (In . Free) (\case{ In (Free n) -> Just n ; _ -> Nothing })

bound_ :: Prism' Type Name
bound_ = prism' (In . Bound) (\case{ In (Bound n) -> Just n ; _ -> Nothing })

hole_ :: Prism' Type Text
hole_ = prism' (In . Hole) (\case{ In (Hole n) -> Just n ; _ -> Nothing })


_ForAll :: Prism' Type (Name ::: Type, Type)
_ForAll = prism' (In . uncurry (:=>)) (\case{ In (t :=> b) -> Just (t, b) ; _ -> Nothing })

_Arrow :: Prism' Type (Type, Type)
_Arrow = prism' (In . uncurry (:->)) (\case{ In (a :-> b) -> Just (a, b) ; _ -> Nothing })

_App :: Prism' Type (Type, Type)
_App = prism' (In . uncurry (:$)) (\case{ In (f :$ a) -> Just (f, a) ; _ -> Nothing })

_Prd :: Prism' Type (Type, Type)
_Prd = prism' (In . uncurry (:*)) (\case{ In (l :* r) -> Just (l, r) ; _ -> Nothing })


_Unit :: Type
_Unit = In Unit

_Type :: Type
_Type = In Type


dropAnn :: Type -> Type
dropAnn e = case out e of
  Ann _ e -> e
  _       -> e


aeq :: Type -> Type -> Bool
aeq = fold $ \ t1 t2 -> case (t1, out t2) of
  (Free  n1,           Free  n2)           -> n1 == n2
  (Bound n1,           Bound n2)           -> n1 == n2
  (Type,               Type)               -> True
  (Unit,               Unit)               -> True
  ((n1 ::: t1) :=> b1, (n2 ::: t2) :=> b2) -> n1 == n2 && t1 t2 && b1 b2
  (f1 :$ a1,           f2 :$ a2)           -> f1 f2 && a1 a2
  (a1 :-> b1,          a2 :-> b2)          -> a1 a2 && b1 b2
  (l1 :* r1,           l2 :* r2)           -> l1 l2 && r1 r2
  (Ann _ t1,           Ann _ t2)           -> t1 t2
  _                                        -> False


data TypeF t
  = Free TName
  | Bound Name
  | Hole Text
  | Type
  | Unit
  | (Name ::: t) :=> t
  | t :$ t
  | t :-> t
  | t :*  t
  | Ann Span t
  deriving (Foldable, Functor, Traversable)

infixr 1 :=>
infixl 9 :$
infixr 2 :->
infixl 7 :*


fold :: (TypeF a -> a) -> Type -> a
fold alg = go
  where
  go = alg . fmap go . out
