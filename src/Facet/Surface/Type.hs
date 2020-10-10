{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Type
( Type(..)
, unForAll
, unApp
, aeq
) where

import Control.Effect.Empty
import Data.Text (Text)
import Facet.Name
import Facet.Syntax
import Text.Parser.Position (Span, Spanned(..))

data Type a
  = Free DName
  | Bound Index
  | Hole Text
  | Type
  | Void
  | Unit
  | (UName ::: Type a) :=> Type a
  | Type a :$ Type a
  | Type a :-> Type a
  | Type a :*  Type a
  | Loc a (Type a)
  deriving (Foldable, Functor, Show, Traversable)

infixr 1 :=>
infixl 9 :$
infixr 2 :->
infixl 7 :*

instance Spanned (Type Span) where
  setSpan = Loc

  dropSpan = \case
    Loc _ d -> dropSpan d
    d       -> d


unForAll :: Has Empty sig m => Type a -> m (UName ::: Type a, Type a)
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unApp :: Has Empty sig m => Type a -> m (Type a, Type a)
unApp = \case{ f :$ a -> pure (f, a) ; _ -> empty }


aeq :: Type a -> Type a -> Bool
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
