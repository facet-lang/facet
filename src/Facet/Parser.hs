module Facet.Parser
( Parser(..)
) where

newtype Parser s a = Parser { runParser :: () }
