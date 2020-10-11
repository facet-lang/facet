{-# LANGUAGE TypeOperators #-}
module Facet.Context
( Context(..)
) where

import           Facet.Name
import qualified Facet.Stack as S
import           Facet.Syntax

newtype Context a = Context { getContext :: S.Stack (UName ::: a) }
