module Facet.Span
( -- * Positions
  Pos(..)
, line_
, column_
  -- * Spans
, Span(..)
, HasSpan(..)
) where

import Control.Lens (Lens', iso, lens)
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


class HasSpan t where
  span_ :: Lens' t Span

  start_, end_ :: Lens' t Pos
  start_ = span_ . lens start (\ p s -> p { start = s })
  end_   = span_ . lens end   (\ p e -> p { end   = e })


instance HasSpan Span where
  span_ = iso id id
