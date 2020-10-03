{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Surface
( EName(..)
, Expr
, global
, bound
, lam
, ($$)
, unit
, (**)
, TName(..)
, Type
, tglobal
, tbound
, (>~>)
, (-->)
, (.$)
, (.*)
, _Unit
, _Type
, Decl
, (>=>)
, (>->)
, (.=)
, Module
, module'
, defTerm
, defType
, (:::)(..)
, Located(..)
) where

import Control.Effect.Parser.Span (Span)
import Facet.Surface.Decl as D
import Facet.Surface.Expr as E
import Facet.Surface.Module as M
import Facet.Surface.Type as T
import Facet.Syntax ((:::)(..))
import Prelude hiding ((**))

class Located expr where
  locate :: Span -> expr -> expr

instance Located E.Expr where
  locate = fmap E.In . E.Ann

instance Located T.Type where
  locate = fmap T.In . T.Ann

instance Located D.Decl where
  locate = fmap D.In . D.Ann

instance Located M.Module where
  locate = fmap M.In . M.Ann
