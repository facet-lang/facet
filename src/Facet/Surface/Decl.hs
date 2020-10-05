{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Decl
( Decl(..)
, (>=>)
, unForAll
, (>->)
, (.=)
, dropLoc
, DeclF(..)
, fold
) where

import Control.Effect.Empty
import Facet.Name
import Facet.Surface.Expr (Expr)
import Facet.Surface.Type (Type)
import Facet.Syntax ((:::)(..))
import Text.Parser.Position (Located(..), Span)

newtype Decl = In { out :: DeclF Decl }

instance Located Decl where
  locate = fmap In . Loc

-- | Universal quantification.
(>=>) :: (Name ::: Type) -> Decl -> Decl
(>=>) = fmap In . (:=>)

infixr 1 >=>

unForAll :: Has Empty sig m => Decl -> m (Name ::: Type, Decl)
unForAll d = case out d of
  t :=> b -> pure (t, b)
  _       -> empty

(>->) :: (Name ::: Type) -> Decl -> Decl
(>->) = fmap In . (:->)

infixr 1 >->

(.=) :: Type -> Expr -> Decl
(.=) = fmap In . (:=)

infix 1 .=


dropLoc :: Decl -> Decl
dropLoc d = case out d of
  Loc _ d -> d
  _       -> d


data DeclF a
  = (Name ::: Type) :=> a
  | (Name ::: Type) :-> a
  | Type := Expr
  | Loc Span a
  deriving (Foldable, Functor, Traversable)

infix 1 :=
infixr 1 :=>
infixr 1 :->


fold :: (DeclF a -> a) -> Decl -> a
fold alg = go
  where
  go = alg . fmap go . out
