-- http://oleg.fi/gists/posts/2019-03-21-flag.html
module Facet.Flag
( Flag
, toFlag
, fromFlag
) where

newtype Flag a = Flag { getFlag :: Bool }
  deriving (Eq, Ord, Show)


toFlag :: a -> Bool -> Flag a
toFlag _ = Flag

fromFlag :: a -> Flag a -> Bool
fromFlag _ = getFlag
