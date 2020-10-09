{-# LANGUAGE DeriveTraversable #-}
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
, TypeF(..)
) where

import Control.Category ((>>>))
import Control.Lens.Prism hiding (_Void)
import Data.Text (Text)
import Facet.Name
import Facet.Syntax
import Text.Parser.Position (Span, Spanned(..))

newtype Type = In { out :: TypeF Type }

instance Spanned Type where
  setSpan = fmap In . Loc

  dropSpan = out >>> \case
    Loc _ d -> dropSpan d
    d       -> In d

global_ :: Prism' Type DName
global_ = prism' (In . Free) (\case{ In (Free n) -> Just n ; _ -> Nothing })

bound_ :: Prism' Type Index
bound_ = prism' (In . Bound) (\case{ In (Bound n) -> Just n ; _ -> Nothing })

hole_ :: Prism' Type Text
hole_ = prism' (In . Hole) (\case{ In (Hole n) -> Just n ; _ -> Nothing })


forAll_ :: Prism' Type (UName ::: Type, Type)
forAll_ = prism' (In . uncurry (:=>)) (\case{ In (t :=> b) -> Just (t, b) ; _ -> Nothing })

arrow_ :: Prism' Type (Type, Type)
arrow_ = prism' (In . uncurry (:->)) (\case{ In (a :-> b) -> Just (a, b) ; _ -> Nothing })

app_ :: Prism' Type (Type, Type)
app_ = prism' (In . uncurry (:$)) (\case{ In (f :$ a) -> Just (f, a) ; _ -> Nothing })

prd_ :: Prism' Type (Type, Type)
prd_ = prism' (In . uncurry (:*)) (\case{ In (l :* r) -> Just (l, r) ; _ -> Nothing })


_Type :: Type
_Type = In Type

_Void :: Type
_Void = In Void

_Unit :: Type
_Unit = In Unit


aeq :: Type -> Type -> Bool
aeq t1 t2 = case (out t1, out t2) of
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


data TypeF t
  = Free DName
  | Bound Index
  | Hole Text
  | Type
  | Void
  | Unit
  | (UName ::: t) :=> t
  | t :$ t
  | t :-> t
  | t :*  t
  | Loc Span t
  deriving (Foldable, Functor, Traversable)

infixr 1 :=>
infixl 9 :$
infixr 2 :->
infixl 7 :*
