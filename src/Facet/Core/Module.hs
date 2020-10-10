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

data Module = Module MName [(QName, Def ::: Type.Type (Either Err))]

data Def
  = DTerm Expr.Expr
  | DType (Type.Type (Either Err))
  | DData [CName ::: Type.Type (Either Err)]
