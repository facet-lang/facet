{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.HOAS
( Type(..)
, Expr(..)
, Circ(..)
) where

import           Control.Monad.Fix (MonadFix)
import           Data.Text (Text)
import qualified Facet.Core as C
import           Facet.Name (Scoped, binderM)
import           Facet.Syntax ((:::)(..))

class C.Type ty => Type ty where
  -- | Universal quantification.
  (>=>) :: MonadFix m => m (Text ::: ty) -> (ty -> m ty) -> m ty
  infixr 1 >=>

  -- FIXME: tupling/unit should take a list of types

class C.Expr expr => Expr ty expr | expr -> ty where
  tlam :: MonadFix m => m Text -> (ty -> m expr) -> m expr
  lam0 :: MonadFix m => m Text -> (expr -> m expr) -> m expr


newtype Circ t = Circ { getCirc :: t }
  deriving (C.Expr, C.Type)

instance (C.Type t, Scoped t) => Type (Circ t) where
  t >=> b = t >>= \ (n ::: t) -> Circ <$> binderM C.tbound ((C.==>) . (::: getCirc t)) n (fmap getCirc . b . Circ)

instance (C.Expr expr, Scoped expr) => Expr (Circ expr) (Circ expr) where
  tlam n b = n >>= \ n -> Circ <$> binderM C.bound C.tlam n (fmap getCirc . b . Circ)
  lam0 n b = n >>= \ n -> Circ <$> binderM C.bound C.lam0 n (fmap getCirc . b . Circ)
