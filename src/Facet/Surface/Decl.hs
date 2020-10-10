{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Decl
( Decl(..)
, forAll_
, bind_
, def_
, DeclF(..)
) where

import Control.Lens.Prism
import Facet.Name
import Facet.Surface.Expr (Expr)
import Facet.Surface.Type (Type)
import Facet.Syntax ((:::)(..))
import Text.Parser.Position (Span)

data Decl = In { ann :: Span, out :: DeclF Decl }

instance Show Decl where
  showsPrec p = showsPrec p . out

forAll_ :: Prism' Decl (Span, (UName ::: Type, Decl))
forAll_ = prism' (uncurry In . fmap (uncurry (:=>))) (\case{ In s (t :=> b) -> Just (s, (t, b)) ; _ -> Nothing })

bind_ :: Prism' Decl (Span, (UName ::: Type, Decl))
bind_ = prism' (uncurry In . fmap (uncurry (:->))) (\case{ In s (t :-> b) -> Just (s, (t, b)) ; _ -> Nothing })

def_ :: Prism' Decl (Span, (Type, Expr))
def_ = prism' (uncurry In . fmap (uncurry (:=))) (\case{ In s (t := e) -> Just (s, (t, e)) ; _ -> Nothing })


data DeclF a
  = (UName ::: Type) :=> a
  | (UName ::: Type) :-> a
  | Type := Expr
  deriving (Foldable, Functor, Show, Traversable)

infix 1 :=
infixr 1 :=>
infixr 1 :->
