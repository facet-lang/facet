module Facet.Parser
( Parser(..)
) where

newtype Parser a = Parser { runParser :: () }
