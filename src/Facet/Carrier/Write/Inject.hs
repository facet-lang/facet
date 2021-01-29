module Facet.Carrier.Write.Inject
( WriteC(..)
) where

import Control.Carrier.Reader
import Control.Monad.IO.Class (MonadIO)

newtype WriteC o p m a = WriteC (ReaderC (p -> o) m a)
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)
