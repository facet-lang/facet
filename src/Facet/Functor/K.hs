module Facet.Functor.K
( K(..)
) where

newtype K a b = K { getK :: a }
