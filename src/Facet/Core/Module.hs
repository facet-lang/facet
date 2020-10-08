{-# LANGUAGE TypeOperators #-}
module Facet.Core.Module
( Module(..)
) where

import qualified Facet.Core as C
import qualified Facet.Core.Expr as Expr
import qualified Facet.Core.Type as Type
import           Facet.Name
import           Facet.Syntax

data Module = Module MName [(QName, C.Def Expr.Expr Type.Type ::: Type.Type)]
