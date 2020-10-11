{-# LANGUAGE TypeOperators #-}
module Facet.Context
( Context(..)
) where

import Facet.Name
import Facet.Stack
import Facet.Syntax

newtype Context a = Context { getContext :: Stack (UName ::: a) }
