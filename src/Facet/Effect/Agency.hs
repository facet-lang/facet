{-# LANGUAGE GADTs #-}
module Facet.Effect.Agency
( Root(..)
, Name(..)
, Agency(..)
) where

data Root
  = Root
  | Name :// String

data Name = Name Root String Int

data Agency m k where
  Scope :: String -> m a -> Agency m a
