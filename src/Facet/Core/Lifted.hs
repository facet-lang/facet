{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Lifted
( -- * Types
  C.Type(tglobal, tbound, _Type, _Unit, (.$), (-->), (.*))
, (>=>)
, C.Interpret(..)
  -- * Expressions
, C.Expr(global, bound, ($$))
, lam0
  -- * Re-exports
, Extends(..)
, (>>>)
, castF
, refl
, strengthen
, weaken
) where

import           Control.Monad.Fix
import           Data.Text (Text)
import qualified Facet.Core as C
import           Facet.Env
import           Facet.Name
import           Facet.Syntax

-- Types

(>=>)
  :: (C.Type ty, Scoped ty, MonadFix m)
  => m (Text ::: ty)
  -> (ty -> m ty)
  -> m ty
t >=> b = t >>= \ (n ::: t) -> binderM C.tbound ((C.==>) . (::: t)) n b

infixr 1 >=>


-- Expressions

lam0
  :: (C.Expr expr, Scoped expr, MonadFix m)
  => Text
  -> (expr -> m expr)
  -> m expr
lam0 = binderM C.bound C.lam0
