module Facet.Span
( -- * Positions
  Pos(..)
, line_
, column_
  -- * Spans
, Span(..)
, start_
, end_
) where

import Control.Lens (Lens', lens)
import Data.Functor.Classes (showsBinaryWith)

-- Positions

data Pos = Pos
  { line   :: {-# UNPACK #-} !Int
  , column :: {-# UNPACK #-} !Int
  }
  deriving (Eq, Ord)

instance Show Pos where
  showsPrec p (Pos l c) = showsBinaryWith showsPrec showsPrec "Pos" p l c

line_, column_ :: Lens' Pos Int
line_   = lens line   (\p l -> p { line   = l })
column_ = lens column (\p l -> p { column = l })


-- Spans

data Span = Span
  { start :: {-# UNPACK #-} !Pos
  , end   :: {-# UNPACK #-} !Pos
  }
  deriving (Eq, Ord)

instance Semigroup Span where
  Span s1 e1 <> Span s2 e2 = Span (min s1 s2) (max e1 e2)

instance Show Span where
  showsPrec p (Span s e) = showsBinaryWith showsPrec showsPrec "Span" p s e

start_, end_ :: Lens' Span Pos
start_ = lens start (\p s -> p { start = s })
end_   = lens end   (\p e -> p { end   = e })
