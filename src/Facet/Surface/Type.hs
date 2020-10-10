{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Type
( Type(..)
, global_
, bound_
, hole_
, forAll_
, arrow_
, app_
, prd_
, _Type
, _Void
, _Unit
, aeq
) where

import Control.Lens.Prism hiding (_Void)
import Data.Text (Text)
import Facet.Name
import Facet.Syntax
import Text.Parser.Position (Span, Spanned(..))

data Type
  = Free DName
  | Bound Index
  | Hole Text
  | Type
  | Void
  | Unit
  | (UName ::: Type) :=> Type
  | Type :$ Type
  | Type :-> Type
  | Type :*  Type
  | Loc Span Type
  deriving (Show)

infixr 1 :=>
infixl 9 :$
infixr 2 :->
infixl 7 :*

instance Spanned Type where
  setSpan = Loc

  dropSpan = \case
    Loc _ d -> dropSpan d
    d       -> d

global_ :: Prism' Type DName
global_ = prism' Free (\case{ Free n -> Just n ; _ -> Nothing })

bound_ :: Prism' Type Index
bound_ = prism' Bound (\case{ Bound n -> Just n ; _ -> Nothing })

hole_ :: Prism' Type Text
hole_ = prism' Hole (\case{ Hole n -> Just n ; _ -> Nothing })


forAll_ :: Prism' Type (UName ::: Type, Type)
forAll_ = prism' (uncurry (:=>)) (\case{ t :=> b -> Just (t, b) ; _ -> Nothing })

arrow_ :: Prism' Type (Type, Type)
arrow_ = prism' (uncurry (:->)) (\case{ a :-> b -> Just (a, b) ; _ -> Nothing })

app_ :: Prism' Type (Type, Type)
app_ = prism' (uncurry (:$)) (\case{ f :$ a -> Just (f, a) ; _ -> Nothing })

prd_ :: Prism' Type (Type, Type)
prd_ = prism' (uncurry (:*)) (\case{ l :* r -> Just (l, r) ; _ -> Nothing })


_Type :: Type
_Type = Type

_Void :: Type
_Void = Void

_Unit :: Type
_Unit = Unit


aeq :: Type -> Type -> Bool
aeq t1 t2 = case (t1, t2) of
  (Free  n1,           Free  n2)           -> n1 == n2
  (Bound n1,           Bound n2)           -> n1 == n2
  (Type,               Type)               -> True
  (Unit,               Unit)               -> True
  ((n1 ::: t1) :=> b1, (n2 ::: t2) :=> b2) -> n1 == n2 && aeq t1 t2 && aeq b1 b2
  (f1 :$ a1,           f2 :$ a2)           -> aeq f1 f2 && aeq a1 a2
  (a1 :-> b1,          a2 :-> b2)          -> aeq a1 a2 && aeq b1 b2
  (l1 :* r1,           l2 :* r2)           -> aeq l1 l2 && aeq r1 r2
  -- FIXME: skip spans one either side independently right up front
  (Loc _ t1,           Loc _ t2)           -> aeq t1 t2
  _                                        -> False
