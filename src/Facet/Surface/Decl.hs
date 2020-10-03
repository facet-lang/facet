{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Decl
( Decl(..)
, DeclF(..)
) where

import           Facet.Name
import qualified Facet.Surface as S
import           Facet.Surface.Expr (Expr)
import           Facet.Surface.Type (Type)
import           Facet.Syntax ((:::)(..))

newtype Decl = In { out :: DeclF Decl }

data DeclF a
  = Type := Expr
  | (Name ::: Type) :=> a
  | (Name ::: Type) :-> a

infix 1 :=
infixr 1 :=>
infixr 1 :->

instance S.Decl Expr Type Decl where
  (.=) = fmap In . (:=)
  (>=>) = fmap In . (:=>)
  (>->) = fmap In . (:->)
