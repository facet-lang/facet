{-# LANGUAGE TypeOperators #-}
module Facet.Module
( Module(..)
) where

import qualified Data.Text as T
import           Facet.Expr
import           Facet.Syntax
import           Facet.Type

data Module
  = Module T.Text Module
  | T.Text :.:. (Expr := Type)

infix 1 :.:.
