module Facet.Show
( Endo
, (<+>)
, (<.>)
, char
, string
, text
, parenIf
, paren
, brace
, bracket
, commaSep
) where

import Data.Foldable (fold)
import Data.List (intersperse)
import Data.Monoid (Endo(..))
import Data.Text (Text, unpack)

(<+>) :: Endo String -> Endo String -> Endo String
a <+> b = a <> char ' ' <> b

(<.>) :: Endo String -> Endo String -> Endo String
a <.> b = a <> char '.' <> b

char :: Char -> Endo String
char = Endo . showChar

string :: String -> Endo String
string = Endo . showString

text :: Text -> Endo String
text = Endo . showString . unpack

parenIf :: Bool -> Endo String -> Endo String
parenIf True  = paren
parenIf False = id

paren, brace, bracket :: Endo String -> Endo String
paren   b = char '(' <> b <> char ')'
brace   b = char '{' <> b <> char '}'
bracket b = char '[' <> b <> char ']'

commaSep :: [Endo String] -> Endo String
commaSep = fold . intersperse (string ", ")
