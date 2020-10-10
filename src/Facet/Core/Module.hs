{-# LANGUAGE TypeOperators #-}
module Facet.Core.Module
( Module(..)
, Def(..)
) where

import Facet.Core.Value (Expr, Type)
import Facet.Name
import Facet.Syntax

data Module f = Module MName [(QName, Def f ::: Type f Level)]

data Def f
  = DTerm (Expr f Level)
  | DType (Type f Level)
  | DData [CName ::: Type f Level]
