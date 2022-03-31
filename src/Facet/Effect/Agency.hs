{-# LANGUAGE GADTs #-}
module Facet.Effect.Agency
( Agency(..)
) where

data Agency m k where
  Scope :: String -> m a -> Agency m a
