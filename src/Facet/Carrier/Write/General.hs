module Facet.Carrier.Write.General
( -- * Write carrier
  WriteC(..)
) where

import Control.Carrier.Reader

newtype WriteC o m a = WriteC (ReaderC (o -> m ()) m a)
