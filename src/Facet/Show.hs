module Facet.Show
( Endo(..)
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
, qname
, name
, op
) where

import Data.Foldable (fold)
import Data.List (intersperse)
import Data.Monoid (Endo(..))
import Data.Text (Text, unpack)
import Facet.Name

-- FIXME: can we do this as a silkscreen printer instead?

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


qname :: Q Name -> Endo String
qname (m :.: n) = foldr (<.>) (name n) (text <$> m)

name :: Name -> Endo String
name = \case
  U t -> string (unpack t)
  O o -> op o

op :: Op -> Endo String
op = \case
  Prefix o   -> text o <> string " _"
  Postfix o  -> string "_ " <> text o
  Infix o    -> string "_ " <> text o <> string " _"
  Outfix o p -> text o <> string " _ " <> text p


newtype Show' = Show' (Int -> String -> String)

instance Semigroup Show' where
  a <> b = Show' $ \ p -> showsPrec p b . showsPrec p a

instance Monoid Show' where
  mempty = Show' (const id)

instance Show Show' where
  showsPrec p (Show' f) = f p
