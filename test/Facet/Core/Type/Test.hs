{-# LANGUAGE TemplateHaskell #-}
module Facet.Core.Type.Test
( tests
) where

import           Control.Lens (review)
import           Facet.Core.Type
import qualified Facet.Name as N
import           Facet.Vars
import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

tests :: IO Bool
tests = checkParallel $$(discover)

prop_fvs_tbound = property $ do
  n <- forAll name
  getFVs (fvs (review bound_ n :: Type)) === bound n

name :: MonadGen m => m (N.Name N.T)
name = N.name N.__ <$> Gen.int (Range.linear 0 100)
