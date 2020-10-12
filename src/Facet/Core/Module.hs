{-# LANGUAGE TypeOperators #-}
module Facet.Core.Module
( Module(..)
, Def(..)
) where

import Facet.Core.Value (Value)
import Facet.Name (CName, MName, QName)
import Facet.Syntax

data Module f a = Module MName [(QName, Def f a ::: Value f a)]

data Def f a
  = DTerm (Value f a)
  | DType (Value f a)
  | DData [CName ::: Value f a]
