module Facet.Source.Reference
( Reference(..)
, path_
, span_
) where

import qualified Facet.Span as Span
import           Fresnel.Lens (Lens', lens)
import           Prelude hiding (span)

data Reference = Reference
  { path :: Maybe FilePath
  , span :: Span.Span
  }

path_ :: Lens' Reference (Maybe FilePath)
path_ = lens path $ \ e path -> e{ path }
{-# INLINE path_ #-}

-- | A lens over the 'Span.Span' from a 'Reference'.
--
-- Note that it is the caller’s responsibility to ensure that this span and the 'lines' are in agreement as to line numbers.
span_ :: Lens' Reference Span.Span
span_ = lens span $ \ e span -> e{ span }
{-# INLINE span_ #-}
