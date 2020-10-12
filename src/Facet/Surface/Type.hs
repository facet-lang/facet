{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Type
( Type(..)
, unForAll
, unApp
, aeq
) where

import Control.Applicative (liftA2)
import Control.Effect.Empty
import Data.Function (on)
import Data.Monoid (First(..))
import Data.Text (Text)
import Facet.Name
import Facet.Syntax

data Type f a
  = Free DName
  | Bound Index
  | Hole Text
  | Type
  | Void
  | Unit
  | (UName ::: f (Type f a)) :=> f (Type f a)
  | f (Type f a) :$ f (Type f a)
  | f (Type f a) :-> f (Type f a)
  | f (Type f a) :*  f (Type f a)
  deriving (Foldable, Functor, Traversable)

deriving instance (Show a, forall a . Show a => Show (f a)) => Show (Type f a)

infixr 1 :=>
infixl 9 :$
infixr 2 :->
infixl 7 :*


unForAll :: Has Empty sig m => Type f a -> m (UName ::: f (Type f a), f (Type f a))
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }

unApp :: Has Empty sig m => Type f a -> m (f (Type f a), f (Type f a))
unApp = \case{ f :$ a -> pure (f, a) ; _ -> empty }


aeq :: Foldable f => Type f a -> Type f a -> Bool
aeq t1 t2 = case (t1, t2) of
  (Free  n1,           Free  n2)           -> n1 == n2
  (Bound n1,           Bound n2)           -> n1 == n2
  (Type,               Type)               -> True
  (Unit,               Unit)               -> True
  ((n1 ::: t1) :=> b1, (n2 ::: t2) :=> b2) -> n1 == n2 && aeq' t1 t2 && aeq' b1 b2
  (f1 :$ a1,           f2 :$ a2)           -> aeq' f1 f2 && aeq' a1 a2
  (a1 :-> b1,          a2 :-> b2)          -> aeq' a1 a2 && aeq' b1 b2
  (l1 :* r1,           l2 :* r2)           -> aeq' l1 l2 && aeq' r1 r2
  -- FIXME: skip spans one either side independently right up front
  _                                        -> False
  where
  aeq' = fmap and . (liftA2 aeq `on` extract)
  extract = getFirst . foldMap (First . Just)
