module Facet.Deriving
( MonadInstance(..)
) where

newtype MonadInstance m a = MonadInstance (m a)
