{-# LANGUAGE TemplateHaskell #-}
module Facet.Core.Test
( tests
) where

import Hedgehog

tests :: IO Bool
tests = checkParallel $$(discover)
