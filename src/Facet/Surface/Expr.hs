{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Surface.Expr
( Expr(..)
, global_
, bound_
, hole_
, lam_
, app_
, unit
, prd_
, comp_
, ExprF(..)
, Comp(..)
, fold
) where

import Control.Category ((>>>))
import Control.Lens.Prism
import Data.Text (Text)
import Facet.Name
import Prelude hiding ((**))
import Text.Parser.Position (Span, Spanned(..))

newtype Expr = In { out :: ExprF Expr }

instance Spanned Expr where
  setSpan = fmap In . Loc

  dropSpan = out >>> \case
    Loc _ d -> dropSpan d
    d       -> In d

global_ :: Prism' Expr DName
global_ = prism' (In . Free) (\case{ In (Free n) -> Just n ; _ -> Nothing })

bound_ :: Prism' Expr Name
bound_ = prism' (In . Bound) (\case{ In (Bound n) -> Just n ; _ -> Nothing })

hole_ :: Prism' Expr Text
hole_ = prism' (In . Hole) (\case{ In (Hole n) -> Just n ; _ -> Nothing })


lam_ :: Prism' Expr (Name, Expr)
lam_ = prism' (In . uncurry Lam) (\case{ In (Lam n b) -> Just (n, b) ; _ -> Nothing })

app_ :: Prism' Expr (Expr, Expr)
app_ = prism' (In . uncurry (:$)) (\case{ In (f :$ a) -> Just (f, a) ; _ -> Nothing })


unit :: Expr
unit = In Unit

prd_ :: Prism' Expr (Expr, Expr)
prd_ = prism' (In . uncurry (:*)) (\case{ In (f :* a) -> Just (f, a) ; _ -> Nothing })

-- FIXME: tupling/unit should take a list of expressions


comp_ :: Prism' Expr (Comp Expr)
comp_ = prism' (In . Comp) (\case{ In (Comp c) -> Just c ; _ -> Nothing })


data ExprF e
  = Free DName
  | Bound Name
  | Hole Text
  | Lam Name e
  | e :$ e
  | Unit
  | e :* e
  | Comp (Comp e)
  | Loc Span e
  deriving (Foldable, Functor, Traversable)

infixl 9 :$
infixl 7 :*


fold :: (ExprF a -> a) -> Expr -> a
fold alg = go
  where
  go = alg . fmap go . out


data Comp e
  = Cases [(Name, e)]
  | Expr e
  deriving (Foldable, Functor, Traversable)
