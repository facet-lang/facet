{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module Facet.Source.Test
( tests
) where

import           Data.List (isPrefixOf)
import qualified Data.List.NonEmpty as NE
import           Facet.Source
import           Facet.Span
import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Prelude hiding (lines)

replace a b = go
  where
  go = \case
    ""                        -> ""
    c:cs
      | a `isPrefixOf` (c:cs) -> b <> go (Prelude.drop (length a) (c:cs))
      | otherwise             -> c : go cs


tests :: IO Bool
tests = checkParallel $$(discover)


prop_sourceFromString_returns_empty_string_for_empty_string = property $
  sourceFromString Nothing 0 "" === Source Nothing (Span (Pos 0 0) (Pos 0 0)) "" (NE.fromList [Line 0 "" EOF])

prop_sourceFromString_returns_two_empty_strings_for_a_newline = property $
  sourceFromString Nothing 0 "\n" === Source Nothing (Span (Pos 0 0) (Pos 1 0)) "\n" (NE.fromList [Line 0 "" LF, Line 1 "" EOF])

prop_returns_one_more_string_than_there_are_newlines = property $ do
  s <- forAll (Gen.string (Range.linear 1 100)
    (Gen.frequency [ (5, Gen.unicode), (1, Gen.element "\t\r\n ") ]))
  length (lines (sourceFromString Nothing 0 s))
    === length (Prelude.filter (`elem` "\r\n") (replace "\r\n" "\n" s)) + 1
