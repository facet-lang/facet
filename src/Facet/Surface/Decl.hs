{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Decl
( Decl(..)
, unForAll
) where

import Control.Effect.Empty
import Facet.Name
import Facet.Surface.Expr (Expr)
import Facet.Surface.Type (Type)
import Facet.Syntax ((:::)(..))

data Decl f a
  = (UName ::: f (Type f a)) :=> f (Decl f a)
  | (UName ::: f (Type f a)) :-> f (Decl f a)
  | f (Type f a) := f (Expr f a)
  deriving (Foldable, Functor, Traversable)

deriving instance (Show a, forall a . Show a => Show (f a)) => Show (Decl f a)

infix 1 :=
infixr 1 :=>
infixr 1 :->


unForAll :: Has Empty sig m => Decl f a -> m (UName ::: f (Type f a), f (Decl f a))
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }
