{-# LANGUAGE TypeOperators #-}
module Facet.Core.Module
( Module(..)
, Def(..)
) where

import Facet.Core.Value (Expr, Type)
import Facet.Name (CName, MName, QName)
import Facet.Syntax

data Module f a = Module MName [(QName, Def f a ::: Type f a)]

data Def f a
  = DTerm (Expr f a)
  | DType (Type f a)
  | DData [CName ::: Type f a]
