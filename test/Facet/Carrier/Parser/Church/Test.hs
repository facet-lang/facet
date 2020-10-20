{-# LANGUAGE TemplateHaskell #-}
module Facet.Carrier.Parser.Church.Test
( tests
) where

import Control.Applicative (Alternative(..))
import Data.Set
import Facet.Carrier.Parser.Church
import Facet.Source
import Facet.Span (Pos(..))
import Hedgehog
import Prelude hiding (lines)
import Text.Parser.Char
import Text.Parser.Combinators

parsesInto :: (Eq a, Show a, MonadTest m) => ParserC (Either (Source, Err)) a -> String -> a -> m ()
parsesInto p s expected = case runParserWithString 0 s p of
  Left  (s, e) -> annotateShow (s, e) <* failure
  Right actual -> actual === expected

failsWith :: (Show a, MonadTest m) => ParserC m a -> String -> (Err -> m ()) -> m ()
failsWith p s f = runParser (const (\ e -> annotateShow e <* failure)) f f (Input (Pos 0 0) s) p

hasExpectation :: MonadTest m => Set String -> Err ->  m ()
hasExpectation expected' Err{ expected } = expected === expected'


tests :: IO Bool
tests = checkParallel $$(discover)


-- position

prop_position_at_start = property $
  parsesInto position "" (Pos 0 0)

prop_position_at_end = property $
  parsesInto (char 'x' *> position) "x" (Pos 0 1)

prop_position_after_newline = property $
  parsesInto (newline *> position) "\n" (Pos 1 0)


-- <?>

prop_label_replaces_labels = property $
  failsWith (char 'a' <?> "c") "b" (hasExpectation (singleton "c"))

prop_label_applies_outermost = property $
  failsWith ((char 'a' <?> "b") <?> "c") "d" (hasExpectation (singleton "c"))

prop_label_is_joined_by_alternation = property $
  failsWith ((char 'a' <?> "b") <|> (char 'c' <?> "d")) "e" (hasExpectation (fromList ["b", "d"]))

prop_label_replaces_joined_labels_of_alternation = property $
  failsWith (((char 'a' <?> "b") <|> (char 'c' <?> "d")) <?> "e") "f" (hasExpectation (singleton "e"))
