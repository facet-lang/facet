{-# LANGUAGE TypeOperators #-}
module Facet.Core.HOAS
( Type(..)
, Expr(..)
, Circ(..)
) where

import           Data.Text (Text)
import qualified Facet.Core as C
import           Facet.Name (Scoped, binder)
import           Facet.Syntax ((:::)(..))

class Type ty where
  tglobal :: Text -> ty

  _Type :: ty
  _Unit :: ty

  -- | Universal quantification.
  (>=>) :: (Text ::: ty) -> (ty -> ty) -> ty
  infixr 1 >=>
  (.$) :: ty -> ty -> ty
  infixl 9 .$

  (-->) :: ty -> ty -> ty
  infixr 2 -->
  (.*) :: ty -> ty -> ty
  infixl 7 .*

  -- FIXME: tupling/unit should take a list of types

class Expr expr where
  global :: Text -> expr
  tlam :: Text -> (expr -> expr) -> expr
  lam0 :: Text -> (expr -> expr) -> expr
  ($$) :: expr -> expr -> expr
  infixl 9 $$


newtype Circ t = Circ { getCirc :: t }

instance (C.Type t, Scoped t) => Type (Circ t) where
  tglobal = Circ . C.tglobal

  _Type = Circ C._Type
  _Unit = Circ C._Unit

  (n ::: t) >=> b = Circ $ binder C.tbound ((C.==>) . (::: getCirc t)) n (getCirc . b . Circ)
  f .$  a = Circ $ getCirc f C..$ getCirc a

  a --> b = Circ $ getCirc a C.--> getCirc b
  l .*  r = Circ $ getCirc l C..*  getCirc r
