{-# LANGUAGE DeriveTraversable #-}
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
, ExprF(..)
) where

import Control.Category ((>>>))
import Control.Lens.Prism
import Data.Text (Text)
import Facet.Name
import Facet.Surface.Comp (Clause)
import Prelude hiding ((**))
import Text.Parser.Position (Span, Spanned(..))

newtype Expr = In { out :: ExprF Expr }
  deriving (Show)

instance Spanned Expr where
  setSpan = fmap In . Loc

  dropSpan = out >>> \case
    Loc _ d -> dropSpan d
    d       -> In d

global_ :: Prism' Expr DName
global_ = prism' (In . Free) (\case{ In (Free n) -> Just n ; _ -> Nothing })

bound_ :: Prism' Expr Index
bound_ = prism' (In . Bound) (\case{ In (Bound n) -> Just n ; _ -> Nothing })

hole_ :: Prism' Expr Text
hole_ = prism' (In . Hole) (\case{ In (Hole n) -> Just n ; _ -> Nothing })


comp_ :: Prism' Expr [Clause Expr]
comp_ = prism' (In . Comp) (\case{ In (Comp cs) -> Just cs ; _ -> Nothing })

app_ :: Prism' Expr (Expr, Expr)
app_ = prism' (In . uncurry (:$)) (\case{ In (f :$ a) -> Just (f, a) ; _ -> Nothing })


unit_ :: Prism' Expr ()
unit_ = prism' (const (In Unit)) (\case{ In Unit -> Just () ; _ -> Nothing })

prd_ :: Prism' Expr (Expr, Expr)
prd_ = prism' (In . uncurry (:*)) (\case{ In (l :* r) -> Just (l, r) ; _ -> Nothing })

-- FIXME: tupling/unit should take a list of expressions


data ExprF e
  = Free DName
  | Bound Index
  | Hole Text
  | Comp [Clause e]
  | e :$ e
  | Unit
  | e :* e
  | Loc Span e
  deriving (Foldable, Functor, Show, Traversable)

infixl 9 :$
infixl 7 :*
