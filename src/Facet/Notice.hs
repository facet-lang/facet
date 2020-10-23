{-# LANGUAGE TypeFamilies #-}
module Facet.Notice
( -- * Notices
  Level(..)
, Notice(..)
, level_
, source_
, reason_
, context_
, reAnnotateNotice
, prettyNotice
, Highlight(..)
) where

import           Control.Lens (Lens', lens)
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Maybe (fromMaybe)
import           Facet.Source (Line(..), LineEnding(..), Source(..))
import qualified Facet.Span as Span
import qualified Prettyprinter as P
import           Silkscreen

-- Notices

data Level
  = Info
  | Warn
  | Error
  deriving (Eq, Ord, Show)

instance Pretty Level where
  pretty = \case
    Info  -> pretty "info"
    Warn  -> pretty "warning"
    Error -> pretty "error"


data Notice a = Notice
  { level   :: !(Maybe Level)
  -- FIXME: support multiple source references for e.g. cyclic import errors
  , source  :: {-# UNPACK #-} !Source
  , reason  :: !(P.Doc a)
  , context :: ![P.Doc a]
  }
  deriving (Show)

level_ :: Lens' (Notice a) (Maybe Level)
level_ = lens level $ \ n level -> n{ level }

source_ :: Lens' (Notice a) Source
source_ = lens source $ \ n source -> n{ source }

reason_ :: Lens' (Notice a) (P.Doc a)
reason_ = lens reason $ \ n reason -> n{ reason }

context_ :: Lens' (Notice a) [P.Doc a]
context_ = lens context $ \ n context -> n{ context }

reAnnotateNotice :: (a -> b) -> (Notice a -> Notice b)
reAnnotateNotice f Notice{ level, source, reason, context} = Notice{ level, source, reason = P.reAnnotate f reason, context = map (P.reAnnotate f) context }


prettyNotice :: Notice a -> P.Doc (Highlight a)
prettyNotice (Notice level (Source path span _ (line:|_)) reason context) = concatWith (surround hardline)
  ( nest 2 (group (fillSep
    [ annotate Path (pretty (fromMaybe "(interactive)" path)) <> colon <> prettySpan span <> colon <> foldMap ((space <>) . (<> colon) . (annotate . Level <*> pretty)) level
    , P.reAnnotate Reason reason
    ]))
  : annotate Gutter (pretty (succ (Span.line (Span.start span)))) <+> align (vcat
    [ annotate Gutter (pretty '|') <+> prettyLine line
    , annotate Gutter (pretty '|') <+> padding span <> annotate Caret (caret (lineLength line) span)
    ])
  : map (P.reAnnotate Context) context)
  where
  prettySpan (Span.Span start end)
    | start == end = pos start
    | otherwise    = pos start <> pretty '-' <> pos end

  pos (Span.Pos l c) = annotate Span (pretty (succ l)) <> colon <> annotate Span (pretty (succ c))

  padding (Span.Span (Span.Pos _ c) _) = pretty (replicate c ' ')

  caret lineLength (Span.Span start@(Span.Pos sl sc) end@(Span.Pos el ec))
    | start == end = pretty '^'
    | sl    == el  = pretty (replicate (ec - sc) '~')
    | otherwise    = pretty ('^' : replicate (lineLength - sc) '~' ++ "…")

  lineLength (Line _ line ending) = length line - case ending of{ CRLF -> 2 ; EOF -> 0 ; _ -> 1 }

  prettyLine (Line _ line end) = pretty line <> annotate End (pretty end)


data Highlight a
  = Path
  | Level Level
  | Span
  | Reason a
  | Gutter
  | End
  | Caret
  | Context a
  deriving (Functor)
