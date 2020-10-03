{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Decl
( Decl(..)
, (>=>)
, (>->)
, (.=)
, DeclF(..)
, fold
) where

import Control.Effect.Parser.Span (Span)
import Facet.Name
import Facet.Surface.Expr (Expr)
import Facet.Surface.Type (Type)
import Facet.Syntax ((:::)(..))

newtype Decl = In { out :: DeclF Decl }

-- | Universal quantification.
(>=>) :: (Name ::: Type) -> Decl -> Decl
(>=>) = fmap In . (:=>)

infixr 1 >=>

(>->) :: (Name ::: Type) -> Decl -> Decl
(>->) = fmap In . (:->)

infixr 1 >->

(.=) :: Type -> Expr -> Decl
(.=) = fmap In . (:=)

infix 1 .=

data DeclF a
  = (Name ::: Type) :=> a
  | (Name ::: Type) :-> a
  | Type := Expr
  | Ann Span a
  deriving (Foldable, Functor, Traversable)

infix 1 :=
infixr 1 :=>
infixr 1 :->


fold :: (DeclF a -> a) -> Decl -> a
fold alg = go
  where
  go = alg . fmap go . out
