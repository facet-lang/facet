{-# LANGUAGE FunctionalDependencies #-}
module Facet.Parser
( Parser(..)
, Parsing(..)
) where

import Control.Applicative

newtype Parser s a = Parser { runParser :: () }

class Alternative p => Parsing s p | p -> s where
  symbol :: s -> p s
  (<?>) :: p a -> (a, String) -> p a
