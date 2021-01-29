module Facet.Carrier.Write.Inject
( WriteC(..)
) where

import Control.Carrier.Reader

newtype WriteC o p m a = WriteC (ReaderC (p -> o) m a)
