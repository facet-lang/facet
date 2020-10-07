{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Decl
( Decl(..)
, forAll_
, bind_
, (.=)
, DeclF(..)
, fold
) where

import Control.Category ((>>>))
import Control.Lens.Prism
import Facet.Name
import Facet.Surface.Expr (Expr)
import Facet.Surface.Type (Type)
import Facet.Syntax ((:::)(..))
import Text.Parser.Position (Span, Spanned(..))

newtype Decl = In { out :: DeclF Decl }

instance Spanned Decl where
  setSpan = fmap In . Loc

  dropSpan = out >>> \case
    Loc _ d -> dropSpan d
    d       -> In d

forAll_ :: Prism' Decl (Name T ::: Type, Decl)
forAll_ = prism' (In . uncurry (:=>)) (\case{ In (t :=> b) -> Just (t, b) ; _ -> Nothing })

bind_ :: Prism' Decl (Name E ::: Type, Decl)
bind_ = prism' (In . uncurry (:->)) (\case{ In (t :-> b) -> Just (t, b) ; _ -> Nothing })

(.=) :: Type -> Expr -> Decl
(.=) = fmap In . (:=)

infix 1 .=


data DeclF a
  = (Name T ::: Type) :=> a
  | (Name E ::: Type) :-> a
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
