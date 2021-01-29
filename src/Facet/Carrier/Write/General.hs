module Facet.Carrier.Write.General
( -- * Write carrier
  WriteC(..)
  -- * Write effect
, module Facet.Effect.Write
) where

import Control.Carrier.Reader
import Facet.Effect.Write

newtype WriteC o m a = WriteC (ReaderC (o -> m ()) m a)
