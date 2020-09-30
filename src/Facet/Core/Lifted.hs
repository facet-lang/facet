{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.Lifted
( -- * Types
  C.Type(..)
, (>=>)
  -- * Expressions
, C.Expr(..)
, tlamM
, lam0M
, C.Module(..)
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
import           Facet.Type

-- Types

(>=>)
  :: (C.Type ty, Scoped ty, MonadFix m)
  => m (Text ::: ty)
  -> (ty -> m ty)
  -> m ty
t >=> b = t >>= \ (n ::: t) -> binderM C.tbound ((C.==>) . (::: t)) n b

infixr 1 >=>


-- Expressions

tlamM
  :: (C.Expr expr, Scoped expr, MonadFix m)
  => Text
  -> (Type -> m expr)
  -> m expr
tlamM = binderM C.tbound C.tlam

lam0M
  :: (C.Expr expr, Scoped expr, MonadFix m)
  => Text
  -> (expr -> m expr)
  -> m expr
lam0M = binderM C.bound C.lam0
