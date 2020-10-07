{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Core
( Type(..)
, Expr(..)
, Module(..)
, Def(..)
) where

import qualified Facet.Core.Pattern as P
import           Facet.Name (CName, E, MName, Name, QName, T)
import           Facet.Syntax ((:::)(..))

class Type ty where
  tglobal :: QName -> ty
  tbound :: Name T -> ty

  _Type :: ty
  -- FIXME: encode these as datatypes
  _Void :: ty
  _Unit :: ty

  -- | Universal quantification.
  (>=>) :: (Name T ::: ty) -> ty -> ty
  infixr 1 >=>
  (.$) :: ty -> ty -> ty
  infixl 9 .$

  (-->) :: ty -> ty -> ty
  infixr 2 -->
  (.*) :: ty -> ty -> ty
  infixl 7 .*

  -- FIXME: tupling/unit should take a list of types


class Expr expr where
  global :: QName -> expr
  bound :: Name E -> expr
  tlam :: Name T -> expr -> expr
  lam :: P.Pattern (Name E) -> expr -> expr
  ($$) :: expr -> expr -> expr
  infixl 9 $$
  unit :: expr
  (**) :: expr -> expr -> expr


data Def expr ty
  = DTerm expr
  | DType ty
  | DData [CName ::: ty]
  deriving (Eq, Ord, Show)


class Module expr ty mod | mod -> expr ty where
  module' :: MName -> [(QName, Def expr ty ::: ty)] -> mod
