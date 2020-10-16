{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
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
import Text.Parser.Position

data Decl a
  = (UName ::: Spanned (Type Spanned a)) :=> Spanned (Decl a)
  | (UName ::: Spanned (Type Spanned a)) :-> Spanned (Decl a)
  | Spanned (Type Spanned a) := Spanned (Expr Spanned a)
  deriving (Foldable, Functor, Show, Traversable)

infix 1 :=
infixr 1 :=>
infixr 1 :->


unForAll :: Has Empty sig m => Decl a -> m (UName ::: Spanned (Type Spanned a), Spanned (Decl a))
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }
