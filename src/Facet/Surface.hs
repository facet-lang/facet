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

import Facet.Surface.Decl as D
import Facet.Surface.Expr as E
import Facet.Surface.Module as M
import Facet.Surface.Type as T
import Facet.Syntax ((:::)(..))
import Prelude hiding ((**))
import Text.Parser.Position (Located(..))
