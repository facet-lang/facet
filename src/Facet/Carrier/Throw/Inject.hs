module Facet.Carrier.Throw.Inject
( -- * Throw carrier
  ThrowC(..)
) where

import Control.Carrier.Reader

newtype ThrowC e f m a = ThrowC (ReaderC (f -> e) m a)
