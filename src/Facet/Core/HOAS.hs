{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core.HOAS
( Type(..)
, Expr(..)
, Circ(..)
) where

import           Control.Applicative (liftA2)
import           Control.Monad.Fix (MonadFix)
import           Data.Text (Text)
import qualified Facet.Core as C
import           Facet.Name (Scoped, binderM)
import           Facet.Syntax ((:::)(..))

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
  tlam :: MonadFix m => m Text -> (ty -> m expr) -> m expr
  lam0 :: MonadFix m => m Text -> (expr -> m expr) -> m expr
  ($$) :: Applicative m => m expr -> m expr -> m expr
  infixl 9 $$


newtype Circ t = Circ { getCirc :: t }

instance (C.Type t, Scoped t) => Type (Circ t) where
  tglobal = pure . Circ . C.tglobal

  _Type = pure $ Circ C._Type
  _Unit = pure $ Circ C._Unit

  t >=> b = t >>= \ (n ::: t) -> Circ <$> binderM C.tbound ((C.==>) . (::: getCirc t)) n (fmap getCirc . b . Circ)
  f .$  a = Circ <$> liftA2 (C..$)  (getCirc <$> f) (getCirc <$> a)

  a --> b = Circ <$> liftA2 (C.-->) (getCirc <$> a) (getCirc <$> b)
  l .*  r = Circ <$> liftA2 (C..*)  (getCirc <$> l) (getCirc <$> r)

instance (C.Expr expr, Scoped expr) => Expr (Circ expr) (Circ expr) where
  global = pure . Circ . C.global
  tlam n b = n >>= \ n -> Circ <$> binderM C.bound C.tlam n (fmap getCirc . b . Circ)
  lam0 n b = n >>= \ n -> Circ <$> binderM C.bound C.lam0 n (fmap getCirc . b . Circ)
  f $$ a = Circ <$> liftA2 (C.$$)  (getCirc <$> f) (getCirc <$> a)
