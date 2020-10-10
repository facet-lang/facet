{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import Text.Parser.Position (Span, Spanned(..))

data Decl a
  = (UName ::: Type a) :=> Decl a
  | (UName ::: Type a) :-> Decl a
  | Type a := Expr a
  | Loc a (Decl a)
  deriving (Foldable, Functor, Show, Traversable)

infix 1 :=
infixr 1 :=>
infixr 1 :->

instance Spanned (Decl Span) where
  setSpan = Loc

  dropSpan = \case
    Loc _ d -> dropSpan d
    d       -> d


unForAll :: Has Empty sig m => Decl a -> m (UName ::: Type a, Decl a)
unForAll = \case{ t :=> b -> pure (t, b) ; _ -> empty }
