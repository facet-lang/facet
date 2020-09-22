{-# LANGUAGE LambdaCase #-}
module Facet.Parser.Notice
( Level(..)
, prettyLevel
, Notice(..)
, prettyNotice
) where

import           Data.List (isSuffixOf)
import           Data.Maybe (fromMaybe)
import           Facet.Parser.Excerpt
import           Facet.Parser.Span as Span
import qualified Prettyprinter as P
import           Prettyprinter.Render.Terminal as ANSI

data Level
  = Warn
  | Error
  deriving (Eq, Ord, Show)

prettyLevel :: Level -> P.Doc AnsiStyle
prettyLevel = \case
  Warn  -> magenta (P.pretty "warning")
  Error -> red     (P.pretty "error")


data Notice = Notice
  { level   :: !(Maybe Level)
  , excerpt :: {-# UNPACK #-} !Excerpt
  , reason  :: !(P.Doc AnsiStyle)
  , context :: ![P.Doc AnsiStyle]
  }
  deriving (Show)

prettyNotice :: Notice -> P.Doc AnsiStyle
prettyNotice (Notice level (Excerpt path text span) reason context) = P.vsep
  ( P.nest 2 (P.group (P.fillSep
    [ bold (P.pretty (fromMaybe "(interactive)" path)) <> P.colon <> pos (start span) <> P.colon <> foldMap ((P.space <>) . (<> P.colon) . prettyLevel) level
    , reason
    ]))
  : blue (P.pretty (succ (Span.line (start span)))) P.<+> P.align (P.vcat
    [ blue (P.pretty '|') P.<+> if "\n" `isSuffixOf` text then P.pretty (init text) <> blue (P.pretty "\\n") else P.pretty text <> blue (P.pretty "<end of input>")
    , blue (P.pretty '|') P.<+> padding span <> caret span
    ])
  : context)
  where
  pos (Pos l c) = bold (P.pretty (succ l)) <> P.colon <> bold (P.pretty (succ c))

  padding (Span (Pos _ c) _) = P.pretty (replicate c ' ')

  caret (Span start@(Pos sl sc) end@(Pos el ec))
    | start == end = green (P.pretty '^')
    | sl    == el  = green (P.pretty (replicate (ec - sc) '~'))
    | otherwise    = green (P.pretty "^…")

  bold = P.annotate ANSI.bold


red, green, blue, magenta :: P.Doc AnsiStyle -> P.Doc AnsiStyle
red     = P.annotate $ color Red
green   = P.annotate $ color Green
blue    = P.annotate $ color Blue
magenta = P.annotate $ color Magenta
