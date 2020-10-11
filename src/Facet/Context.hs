{-# LANGUAGE TypeOperators #-}
module Facet.Context
( Context(..)
, (|-)
) where

import           Control.Effect.Reader
import           Facet.Name
import qualified Facet.Stack as S
import           Facet.Syntax

newtype Context a = Context { getContext :: S.Stack (UName ::: a) }


(|-) :: Has (Reader (Context a)) sig m => UName ::: a -> m b -> m b
t |- m = local (Context . (S.:> t) . getContext) m

infix 1 |-
