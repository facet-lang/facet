{-# LANGUAGE TypeOperators #-}
module Facet.Core.Module
( Module(..)
, Def(..)
) where

import Facet.Core.Value (Value)
import Facet.Name (CName, MName, QName)
import Facet.Syntax

data Module a = Module MName [(QName, Def a ::: Value a)]

data Def a
  = DTerm (Value a)
  | DType (Value a)
  | DData [CName ::: Value a]
