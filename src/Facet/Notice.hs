module Facet.Notice
( -- * Notices
  Level(..)
, Notice(..)
, level_
, source_
, reason_
, context_
, reAnnotateNotice
, Style(..)
, identityStyle
, prettyNoticeWith
, prettyNotice
) where

import           Control.Lens (Lens', lens)
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Maybe (fromMaybe)
import           Facet.Source (Line(..), LineEnding(..), Source(..))
import qualified Facet.Span as Span
import qualified Prettyprinter as P
import           Silkscreen
import           System.Console.ANSI

-- Notices

data Level
  = Warn
  | Error
  deriving (Eq, Ord, Show)

instance Pretty Level where
  pretty = \case
    Warn  -> pretty "warning"
    Error -> pretty "error"


data Notice a = Notice
  { level   :: !(Maybe Level)
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


data Style a = Style
  { pathStyle   :: P.Doc a -> P.Doc a
  , levelStyle  :: Level -> P.Doc a -> P.Doc a
  , posStyle    :: P.Doc a -> P.Doc a
  , gutterStyle :: P.Doc a -> P.Doc a
  , eofStyle    :: P.Doc a -> P.Doc a
  , caretStyle  :: P.Doc a -> P.Doc a
  }

identityStyle :: Style a
identityStyle = Style
  { pathStyle   = id
  , levelStyle  = const id
  , posStyle    = id
  , gutterStyle = id
  , eofStyle    = id
  , caretStyle  = id
  }

prettyNoticeWith :: Style a -> Notice a -> P.Doc a
prettyNoticeWith Style{ pathStyle, levelStyle, posStyle, gutterStyle, eofStyle, caretStyle } (Notice level (Source path span _ (line:|_)) reason context) = concatWith (surround hardline)
  ( nest 2 (group (fillSep
    [ pathStyle (pretty (fromMaybe "(interactive)" path)) <> colon <> pos (Span.start span) <> colon <> foldMap ((space <>) . (<> colon) . (levelStyle <*> pretty)) level
    , reason
    ]))
  : gutterStyle (pretty (succ (Span.line (Span.start span)))) <+> align (vcat
    [ gutterStyle (pretty '|') <+> prettyLine line
    , gutterStyle (pretty '|') <+> padding span <> caret (lineLength line) span
    ])
  : context)
  where
  pos (Span.Pos l c) = posStyle (pretty (succ l)) <> colon <> posStyle (pretty (succ c))

  padding (Span.Span (Span.Pos _ c) _) = pretty (replicate c ' ')

  caret lineLength (Span.Span start@(Span.Pos sl sc) end@(Span.Pos el ec))
    | start == end = caretStyle (pretty '^')
    | sl    == el  = caretStyle (pretty (replicate (ec - sc) '~'))
    | otherwise    = caretStyle (pretty ('^' : replicate (lineLength - sc) '~' ++ "…"))

  lineLength (Line _ line ending) = length line - case ending of{ CRLF -> 2 ; EOF -> 0 ; _ -> 1 }

  prettyLine (Line _ line end) = pretty line <> eofStyle (pretty end)


prettyNotice :: Notice [SGR] -> P.Doc [SGR]
prettyNotice = prettyNoticeWith sgrStyle


-- FIXME: figure out some sort of more semantic styling annotations, annotate into that, and then map it onto a configurable stylesheet describing RGB &c.
sgrStyle :: Style [SGR]
sgrStyle = Style
  { pathStyle   = annotate [SetConsoleIntensity BoldIntensity]
  , levelStyle  = \case
    Warn  -> annotate [SetColor Foreground Vivid Magenta]
    Error -> annotate [SetColor Foreground Vivid Red]
  , posStyle    = annotate [SetConsoleIntensity BoldIntensity]
  , gutterStyle = annotate [SetColor Foreground Vivid Blue]
  , eofStyle    = annotate [SetColor Foreground Vivid Blue]
  , caretStyle  = annotate [SetColor Foreground Vivid Green]
  }
