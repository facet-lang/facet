{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Expr
( EName(..)
, Expr(..)
, global
, bound
, lam
, unLam
, _Lam
, ($$)
, unApp
, unit
, (**)
, dropAnn
, ExprF(..)
, fold
) where

import Control.Effect.Empty
import Control.Lens.Prism
import Data.String (IsString(..))
import Data.Text (Text)
import Facet.Name
import Prelude hiding ((**))
import Prettyprinter (Pretty)
import Text.Parser.Position (Located(..), Span)

newtype EName = EName { getEName :: Text }
  deriving (Eq, IsString, Ord, Pretty, Show)

newtype Expr = In { out :: ExprF Expr }

instance Located Expr where
  locate = fmap In . Ann

global :: EName -> Expr
global = In . Free

bound :: Name -> Expr
bound = In . Bound

lam :: Name -> Expr -> Expr
lam = fmap In . Lam

unLam :: Has Empty sig m => Expr -> m (Name, Expr)
unLam e = case out e of
  Lam n b -> pure (n, b)
  _       -> empty

_Lam :: Prism' Expr (Name, Expr)
_Lam = prism' (uncurry lam) (\case{ In (Lam n b) -> Just (n, b) ; _ -> Nothing })


($$) :: Expr -> Expr -> Expr
($$) = fmap In . (:$)

infixl 9 $$

unApp :: Has Empty sig m => Expr -> m (Expr, Expr)
unApp e = case out e of
  f :$ a -> pure (f, a)
  _      -> empty


unit :: Expr
unit = In Unit

-- | Tupling.
(**) :: Expr -> Expr -> Expr
(**) = fmap In . (:*)

-- FIXME: tupling/unit should take a list of expressions


dropAnn :: Expr -> Expr
dropAnn e = case out e of
  Ann _ e -> e
  _       -> e


data ExprF e
  = Free EName
  | Bound Name
  | Lam Name e
  | e :$ e
  | Unit
  | e :* e
  | Ann Span e
  deriving (Foldable, Functor, Traversable)

infixl 9 :$
infixl 7 :*


fold :: (ExprF a -> a) -> Expr -> a
fold alg = go
  where
  go = alg . fmap go . out
