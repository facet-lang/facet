{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
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

data Expr
  = Free DName
  | Bound Index
  | Hole Text
  | Comp [Clause Expr]
  | Expr :$ Expr
  | Unit
  | Expr :* Expr
  | Loc Span Expr
  deriving (Show)

infixl 9 :$
infixl 7 :*

instance Spanned Expr where
  setSpan = Loc

  dropSpan = \case
    Loc _ d -> dropSpan d
    d       -> d

global_ :: Prism' Expr DName
global_ = prism' Free (\case{ Free n -> Just n ; _ -> Nothing })

bound_ :: Prism' Expr Index
bound_ = prism' Bound (\case{ (Bound n) -> Just n ; _ -> Nothing })

hole_ :: Prism' Expr Text
hole_ = prism' Hole (\case{ (Hole n) -> Just n ; _ -> Nothing })


comp_ :: Prism' Expr [Clause Expr]
comp_ = prism' Comp (\case{ Comp cs -> Just cs ; _ -> Nothing })

app_ :: Prism' Expr (Expr, Expr)
app_ = prism' (uncurry (:$)) (\case{ f :$ a -> Just (f, a) ; _ -> Nothing })


unit_ :: Prism' Expr ()
unit_ = prism' (const (Unit)) (\case{ Unit -> Just () ; _ -> Nothing })

prd_ :: Prism' Expr (Expr, Expr)
prd_ = prism' (uncurry (:*)) (\case{ l :* r -> Just (l, r) ; _ -> Nothing })

-- FIXME: tupling/unit should take a list of expressions
