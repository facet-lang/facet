{-# LANGUAGE LambdaCase #-}
module Facet.Parser.Source
( Source(..)
, sourceFromString
, substring
, (!)
) where

import Facet.Parser.Span
import Prelude hiding (lines)

data Source = Source
  { path  :: Maybe FilePath
  , lines :: [String]
  }
  deriving (Eq, Ord, Show)

sourceFromString :: Maybe FilePath -> String -> Source
sourceFromString path = Source path . go
  where
  go = \case
    "" -> [""]
    s  -> let (line, rest) = takeLine s in line : either (const []) go rest
{-# inline sourceFromString #-}

takeLine :: String -> (String, Either String String)
takeLine = go id where
  go line = \case
    ""        -> (line "", Left "")
    '\r':rest -> case rest of
      '\n':rest -> (line "\r\n", Right rest)
      _         -> (line "\r", Right rest)
    '\n':rest -> (line "\n", Right rest)
    c   :rest -> go (line . (c:)) rest
{-# inline takeLine #-}

substring :: Source -> Span -> String
substring source (Span (Pos sl sc) (Pos el ec)) = concat (onHead (drop sc) (onLast (take ec) (drop sl (take (el+1) (lines source)))))
  where
  onHead f = \case
    []   -> []
    x:xs -> f x : xs
  onLast f = go
    where
    go = \case
      []   -> []
      [x]  -> [f x]
      x:xs -> x:go xs

(!) :: Source -> Pos -> String
Source _ lines ! pos = lines !! line pos
{-# INLINE (!) #-}

infixl 9 !
