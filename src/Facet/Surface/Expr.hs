{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
module Facet.Surface.Expr
( Expr(..)
, unApp
, Clause(..)
, unClause
) where

import Control.Effect.Empty
import Data.Text (Text)
import Facet.Name
import Facet.Surface.Pattern (Pattern)
import Prelude hiding ((**))

data Expr f a
  = Free DName
  | Bound Index
  | Hole Text
  | Comp [f (Clause f a)]
  | f (Expr f a) :$ f (Expr f a)
  | Unit
  | f (Expr f a) :* f (Expr f a)
  -- FIXME: tupling/unit should take a list of expressions
  deriving (Foldable, Functor, Traversable)

deriving instance (Show a, forall a . Show a => Show (f a)) => Show (Expr f a)

infixl 9 :$
infixl 7 :*


unApp :: Has Empty sig m => Expr f a -> m (f (Expr f a), f (Expr f a))
unApp = \case
  f :$ a -> pure (f, a)
  _      -> empty


data Clause f a
  = Clause (f (Pattern f UName)) (f (Clause f a))
  | Body (f (Expr f a))
  deriving (Foldable, Functor, Traversable)

deriving instance (Show a, forall a . Show a => Show (f a)) => Show (Clause f a)


unClause :: Has Empty sig m => Clause f a -> m (f (Pattern f UName), f (Clause f a))
unClause = \case{ Clause p c -> pure (p, c) ; _ -> empty }
