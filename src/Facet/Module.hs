{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Module
( Module(..)
) where

import qualified Data.Text as T
import qualified Facet.Core as C
import           Facet.Expr
import           Facet.Syntax
import           Facet.Type

data Module
  = Module T.Text Module
  | T.Text :.:. (Expr := Type)

infix 1 :.:.

instance C.Module Expr Type Module where
  module' = Module
  (.:.) = (:.:.)
