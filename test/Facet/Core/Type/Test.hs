{-# LANGUAGE TemplateHaskell #-}
module Facet.Core.Type.Test
( tests
-- , name
) where

-- import           Facet.Core.Type
-- import           Facet.Name
-- import           Facet.Vars
import           Hedgehog
-- import qualified Hedgehog.Gen as Gen
-- import qualified Hedgehog.Range as Range

tests :: IO Bool
tests = checkParallel $$(discover)

-- prop_fvs_tbound = property $ do
--   n <- forAll name
--   getFVs (fvs (bound n :: Type)) === boundVar n

-- name :: MonadGen m => m (Name T)
-- name = Name (UName __) <$> Gen.int (Range.linear 0 100)
