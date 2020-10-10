{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Decl
( Decl(..)
, forAll_
, bind_
, def_
) where

import Control.Lens.Prism
import Facet.Name
import Facet.Surface.Expr (Expr)
import Facet.Surface.Type (Type)
import Facet.Syntax ((:::)(..))
import Text.Parser.Position (Span, Spanned(..))

data Decl a
  = (UName ::: Type a) :=> Decl a
  | (UName ::: Type a) :-> Decl a
  | Type a := Expr
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

forAll_ :: Prism' (Decl a) (UName ::: Type a, Decl a)
forAll_ = prism' (uncurry (:=>)) (\case{ t :=> b -> Just (t, b) ; _ -> Nothing })

bind_ :: Prism' (Decl a) (UName ::: Type a, Decl a)
bind_ = prism' (uncurry (:->)) (\case{ t :-> b -> Just (t, b) ; _ -> Nothing })

def_ :: Prism' (Decl a) (Type a, Expr)
def_ = prism' (uncurry (:=)) (\case{ t := e -> Just (t, e) ; _ -> Nothing })
