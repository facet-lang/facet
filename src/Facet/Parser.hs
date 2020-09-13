{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Facet.Parser
( Parsing(..)
, Parser(..)
, Nullable(..)
, First(..)
) where

import           Control.Applicative
import           Data.Coerce
import qualified Data.Set as Set

class Alternative p => Parsing s p | p -> s where
  symbol :: s -> p s
  (<?>) :: p a -> (a, String) -> p a
  infixl 2 <?>

newtype Parser s a = Parser { runParser :: () }

newtype Nullable s a = Nullable { getNullable :: Bool }

instance Functor (Nullable s) where
  fmap _ = coerce

instance Applicative (Nullable s) where
  pure _ = Nullable True
  (<*>) = coerce (&&)

instance Alternative (Nullable s) where
  empty = Nullable False
  (<|>) = coerce (||)

instance Parsing s (Nullable s) where
  symbol _ = Nullable False
  _ <?> _ = Nullable False


data First s a = First
  { isNullable :: Nullable s a
  , getFirst :: Set.Set s
  }

instance Functor (First s) where
  fmap _ = coerce
