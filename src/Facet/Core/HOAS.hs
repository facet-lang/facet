{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.HOAS
( Type(..)
, Expr(..)
) where

import Control.Monad.Fix (MonadFix)
import Data.Text (Text)
import Facet.Syntax ((:::)(..))

class Type ty where
  tglobal :: Applicative m => Text -> m ty

  _Type :: Applicative m => m ty
  _Unit :: Applicative m => m ty

  -- | Universal quantification.
  (>=>) :: MonadFix m => m (Text ::: ty) -> (ty -> m ty) -> m ty
  infixr 1 >=>
  (.$) :: Applicative m => m ty -> m ty -> m ty
  infixl 9 .$

  (-->) :: Applicative m => m ty -> m ty -> m ty
  infixr 2 -->
  (.*) :: Applicative m => m ty -> m ty -> m ty
  infixl 7 .*

  -- FIXME: tupling/unit should take a list of types

class Expr ty expr | expr -> ty where
  global :: Applicative m => Text -> m expr
  tlam :: MonadFix m => Text -> (expr -> m expr) -> m expr
  lam0 :: MonadFix m => Text -> (expr -> m expr) -> m expr
  ($$) :: Applicative m => m expr -> m expr -> m expr
  infixl 9 $$
