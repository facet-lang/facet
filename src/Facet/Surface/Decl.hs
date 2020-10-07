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
, fold
) where

import Control.Lens.Prism
import Facet.Name
import Facet.Surface.Expr (Expr)
import Facet.Surface.Type (Type)
import Facet.Syntax ((:::)(..))
import Text.Parser.Position (Span)

data Decl = In { ann :: Span, out :: DeclF Decl }

forAll_ :: Prism' Decl (Span, (Name T ::: Type, Decl))
forAll_ = prism' (uncurry In . fmap (uncurry (:=>))) (\case{ In s (t :=> b) -> Just (s, (t, b)) ; _ -> Nothing })

bind_ :: Prism' Decl (Span, (Name E ::: Type, Decl))
bind_ = prism' (uncurry In . fmap (uncurry (:->))) (\case{ In s (t :-> b) -> Just (s, (t, b)) ; _ -> Nothing })

def_ :: Prism' Decl (Span, (Type, Expr))
def_ = prism' (uncurry In . fmap (uncurry (:=))) (\case{ In s (t := e) -> Just (s, (t, e)) ; _ -> Nothing })


data DeclF a
  = (Name T ::: Type) :=> a
  | (Name E ::: Type) :-> a
  | Type := Expr
  deriving (Foldable, Functor, Traversable)

infix 1 :=
infixr 1 :=>
infixr 1 :->


fold :: (Span -> DeclF a -> a) -> Decl -> a
fold alg = go
  where
  go = alg . ann <*> fmap go . out
