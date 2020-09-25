{-# LANGUAGE TypeOperators #-}
module Facet.Syntax.Common
( (:::)(..)
) where

data a ::: b = a ::: b
  deriving (Eq, Ord, Show)

infix 5 :::
