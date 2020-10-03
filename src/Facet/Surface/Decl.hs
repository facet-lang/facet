{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Decl
( Decl(..)
, DeclF(..)
, fold
) where

import           Control.Effect.Parser.Span (Span)
import           Facet.Name
import qualified Facet.Surface as S
import           Facet.Surface.Expr (Expr)
import           Facet.Surface.Type (Type)
import           Facet.Syntax ((:::)(..))

newtype Decl = In { out :: DeclF Decl }

data DeclF a
  = (Name ::: Type) :=> a
  | (Name ::: Type) :-> a
  | Type := Expr
  | Ann Span a
  deriving (Foldable, Functor, Traversable)

infix 1 :=
infixr 1 :=>
infixr 1 :->

instance S.Decl Expr Type Decl where
  (.=) = fmap In . (:=)
  (>=>) = fmap In . (:=>)
  (>->) = fmap In . (:->)

instance S.Located Decl where
  locate = fmap In . Ann


fold :: (DeclF a -> a) -> Decl -> a
fold alg = go
  where
  go = alg . fmap go . out
