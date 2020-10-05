{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Expr
( EName(..)
, Expr(..)
, global_
, bound_
, _Lam
, _App
, unit
, _Prd
, dropAnn
, ExprF(..)
, fold
) where

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

global_ :: Prism' Expr EName
global_ = prism' (In . Free) (\case{ In (Free n) -> Just n ; _ -> Nothing })

bound_ :: Prism' Expr Name
bound_ = prism' (In . Bound) (\case{ In (Bound n) -> Just n ; _ -> Nothing })


_Lam :: Prism' Expr (Name, Expr)
_Lam = prism' (In . uncurry Lam) (\case{ In (Lam n b) -> Just (n, b) ; _ -> Nothing })

_App :: Prism' Expr (Expr, Expr)
_App = prism' (In . uncurry (:$)) (\case{ In (f :$ a) -> Just (f, a) ; _ -> Nothing })


unit :: Expr
unit = In Unit

_Prd :: Prism' Expr (Expr, Expr)
_Prd = prism' (In . uncurry (:*)) (\case{ In (f :* a) -> Just (f, a) ; _ -> Nothing })

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
