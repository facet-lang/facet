module Facet.Carrier.Error.Lens
( ErrorC(..)
) where

import Control.Carrier.Reader
import Control.Lens (APrism')

newtype ErrorC e f m a = ErrorC (ReaderC (APrism' e f) m a)
