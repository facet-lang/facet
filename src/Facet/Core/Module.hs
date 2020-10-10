{-# LANGUAGE TypeOperators #-}
module Facet.Core.Module
( Module(..)
, Def(..)
) where

import qualified Facet.Core.Expr as Expr
import qualified Facet.Core.Type as Type
import           Facet.Error
import           Facet.Name
import           Facet.Syntax

data Module = Module MName [(QName, Def (Either Err) ::: Type.Type (Either Err))]

data Def f
  = DTerm (Expr.Expr f)
  | DType (Type.Type f)
  | DData [CName ::: Type.Type f]
