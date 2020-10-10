{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Expr
( Expr(..)
, global_
, bound_
, hole_
, comp_
, app_
, unit_
, prd_
) where

import Control.Lens.Prism
import Data.Text (Text)
import Facet.Name
import Facet.Surface.Comp (Clause)
import Prelude hiding ((**))
import Text.Parser.Position (Span, Spanned(..))

data Expr a
  = Free DName
  | Bound Index
  | Hole Text
  | Comp [Clause Expr a]
  | Expr a :$ Expr a
  | Unit
  | Expr a :* Expr a
  | Loc Span (Expr a)
  deriving (Foldable, Functor, Show, Traversable)

infixl 9 :$
infixl 7 :*

instance Spanned (Expr Span) where
  setSpan = Loc

  dropSpan = \case
    Loc _ d -> dropSpan d
    d       -> d

global_ :: Prism' (Expr a) DName
global_ = prism' Free (\case{ Free n -> Just n ; _ -> Nothing })

bound_ :: Prism' (Expr a) Index
bound_ = prism' Bound (\case{ (Bound n) -> Just n ; _ -> Nothing })

hole_ :: Prism' (Expr a) Text
hole_ = prism' Hole (\case{ (Hole n) -> Just n ; _ -> Nothing })


comp_ :: Prism' (Expr a) [Clause Expr a]
comp_ = prism' Comp (\case{ Comp cs -> Just cs ; _ -> Nothing })

app_ :: Prism' (Expr a) (Expr a, Expr a)
app_ = prism' (uncurry (:$)) (\case{ f :$ a -> Just (f, a) ; _ -> Nothing })


unit_ :: Prism' (Expr a) ()
unit_ = prism' (const (Unit)) (\case{ Unit -> Just () ; _ -> Nothing })

prd_ :: Prism' (Expr a) (Expr a, Expr a)
prd_ = prism' (uncurry (:*)) (\case{ l :* r -> Just (l, r) ; _ -> Nothing })

-- FIXME: tupling/unit should take a list of expressions
