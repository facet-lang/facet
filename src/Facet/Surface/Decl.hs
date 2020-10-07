{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface.Decl
( Decl(..)
, (>=>)
, forAll_
, (>->)
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

-- | Universal quantification.
(>=>) :: (TLocal ::: Type) -> Decl -> Decl
(>=>) = fmap In . (:=>)

infixr 1 >=>

forAll_ :: Prism' Decl (TLocal ::: Type, Decl)
forAll_ = prism' (In . uncurry (:=>)) (\case{ In (t :=> b) -> Just (t, b) ; _ -> Nothing })

(>->) :: (ELocal ::: Type) -> Decl -> Decl
(>->) = fmap In . (:->)

infixr 1 >->

(.=) :: Type -> Expr -> Decl
(.=) = fmap In . (:=)

infix 1 .=


data DeclF a
  = (TLocal ::: Type) :=> a
  | (ELocal ::: Type) :-> a
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
