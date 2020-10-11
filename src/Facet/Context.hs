{-# LANGUAGE TypeOperators #-}
module Facet.Context
( Context(..)
, (!?)
, level
, (|-)
, lookupBound
, runContext
) where

import           Control.Carrier.Reader
import           Facet.Name
import qualified Facet.Stack as S
import           Facet.Syntax

newtype Context a = Context { getContext :: S.Stack (UName ::: a) }

level :: Context a -> Level
level (Context c) = Level (length c)

(!?) :: Context a -> Index -> Maybe (UName ::: a)
c !? i = getContext c S.!? getIndex i


(|-) :: Has (Reader (Context a)) sig m => UName ::: a -> m b -> m b
t |- m = local (Context . (S.:> t) . getContext) m

infix 1 |-

lookupBound :: Has (Reader (Context a)) sig m => Index -> m (Maybe (UName ::: a))
lookupBound = asks . flip (!?)

runContext :: ReaderC (Context a) m a -> m a
runContext = runReader (Context S.Nil)
