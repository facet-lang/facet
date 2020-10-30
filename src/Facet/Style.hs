{-# LANGUAGE TypeFamilies #-}
module Facet.Style
( Style(..)
, terminalStyle
, terminalCodeStyle
  -- * Pretty-printing
, prettyCode
, prettyNotice
) where

import           Data.Colour.RGBSpace.HSL
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Maybe (fromMaybe)
import           Facet.Name (Level(getLevel), Meta(..))
import qualified Facet.Notice as Notice
import           Facet.Pretty
import           Facet.Print as Print
import           Facet.Source
import qualified Facet.Span as Span
import qualified Prettyprinter as P
import           Silkscreen

data Style
  = Failure
  | Success
  | Progress
  | Command
  | Code Print.Highlight
  | Path
  | Level Notice.Level
  | Span
  | Reason
  | Gutter
  | End
  | Caret
  | Context


terminalStyle :: Style -> [SGR]
terminalStyle = \case
  Failure  -> [setRGB (hsl 0 1 0.5)]
  Success  -> [setRGB (hsl 120 1 0.5)]
  Progress -> [setRGB (hsl 0 0 0.5), setBold]
  Command  -> [setRGB (hsl 180 1 0.5)]
  Code s   -> terminalCodeStyle s
  Path      -> [setBold]
  Level l -> case l of
    Notice.Info  -> [setRGB (hsl 0 0 0.5)]
    Notice.Warn  -> [setRGB (hsl 300 1 0.5)]
    Notice.Error -> [setRGB (hsl 0 1 0.5)]
  Span      -> [setBold]
  Reason    -> []
  Gutter    -> [setRGB (hsl 230 1 0.7)]
  End       -> [setRGB (hsl 230 1 0.7)]
  Caret     -> [setRGB (hsl 120 0.8 0.4)]
  Context   -> []

terminalCodeStyle :: Print.Highlight -> [SGR]
terminalCodeStyle = \case
  Nest i  -> [setRGB (pick i 0.4 0.8)]
  Name i  -> [setRGB (pick (-getLevel i) 0.8 0.6)]
  Keyword -> [setRGB (hsl 300 0.7 0.4)]
  Op      -> [setRGB (hsl 180 0.7 0.4)]
  Type    -> [setRGB (hsl 60 0.5 0.5)]
  Con     -> [setRGB (hsl 15 0.8 0.5)]
  Lit     -> [setBold]
  Hole m  -> [setBold, setRGB (pick (-getMeta m) 0.5 0.45)]
  where
  pick i s l = hsl (fromIntegral i * phi * 30) s l
  phi = 1.618033988749895


-- Pretty-printing

prettyCode :: Print -> Doc Style
prettyCode = P.reAnnotate Code . getPrint


prettyNotice :: Notice.Notice (P.Doc Style) -> P.Doc Style
prettyNotice (Notice.Notice level Nothing reason context) = concatWith (surround hardline)
  ( nest 2 (group (fillSep
    [ foldMap ((space <>) . (<> colon) . (annotate . Level <*> pretty)) level
    , annotate Reason reason
    ]))
  : (context >>= \ ctx -> [ mempty, annotate Context ctx ]))
prettyNotice (Notice.Notice level (Just (Source path span _ (line:|_))) reason context) = concatWith (surround hardline)
  ( nest 2 (group (fillSep
    [ annotate Path (pretty (fromMaybe "(interactive)" path)) <> colon <> prettySpan span <> colon <> foldMap ((space <>) . (<> colon) . (annotate . Level <*> pretty)) level
    , annotate Reason reason
    ]))
  : annotate Gutter (pretty (succ (Span.line (Span.start span)))) <+> align (vcat
    [ annotate Gutter (pretty '|') <+> prettyLine line
    , annotate Gutter (pretty '|') <+> padding span <> annotate Caret (caret (lineLength line) span)
    ])
  : (context >>= \ ctx -> [ mempty, annotate Context ctx ]))
  where
  prettySpan (Span.Span start end)
    | start == end                     = pos start
    | Span.line start == Span.line end = pos start <> pretty '-' <> coord (Span.column end)
    | otherwise                        = pos start <> pretty '-' <> pos end

  pos (Span.Pos l c) = coord l <> colon <> coord c
  coord = annotate Span . pretty . succ

  padding (Span.Span (Span.Pos _ c) _) = pretty (replicate c ' ')

  caret lineLength (Span.Span start@(Span.Pos sl sc) end@(Span.Pos el ec))
    | start == end = pretty '^'
    | sl    == el  = pretty (replicate (ec - sc) '~')
    | otherwise    = pretty ('^' : replicate (lineLength - sc) '~' ++ "…")

  lineLength (Line _ line ending) = length line - case ending of{ CRLF -> 2 ; EOF -> 0 ; _ -> 1 }

  prettyLine (Line _ line end) = pretty line <> annotate End (pretty end)
