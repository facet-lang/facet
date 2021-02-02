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
, prec
, setPrec
, qname
, name
, op
, ShowP(..)
) where

import Data.Foldable (fold)
import Data.List (intersperse)
import Data.Monoid (Endo(..))
import Data.Text (Text, unpack)
import Facet.Name

-- FIXME: can we do this as a silkscreen printer instead?

(<+>) :: ShowP -> ShowP -> ShowP
a <+> b = a <> char ' ' <> b

(<.>) :: ShowP -> ShowP -> ShowP
a <.> b = a <> char '.' <> b

char :: Char -> ShowP
char = ShowP . const . showChar

string :: String -> ShowP
string = ShowP . const . showString

text :: Text -> ShowP
text = ShowP . const . showString . unpack

parenIf :: Bool -> ShowP -> ShowP
parenIf True  = paren
parenIf False = id

paren, brace, bracket :: ShowP -> ShowP
paren   b = char '(' <> b <> char ')'
brace   b = char '{' <> b <> char '}'
bracket b = char '[' <> b <> char ']'

commaSep :: [ShowP] -> ShowP
commaSep = fold . intersperse (string ", ")


prec :: Int -> ShowP -> ShowP
prec p s = ShowP (\ p' -> showsPrec p' (parenIf (p' > p) s))

setPrec :: Int -> ShowP -> ShowP
setPrec p (ShowP f) = ShowP $ const (f p)


qname :: Q Name -> ShowP
qname (m :.: n) = foldr (<.>) (name n) (text <$> m)

name :: Name -> ShowP
name = \case
  U t -> string (unpack t)
  O o -> op o

op :: Op -> ShowP
op = \case
  Prefix o   -> text o <> string " _"
  Postfix o  -> string "_ " <> text o
  Infix o    -> string "_ " <> text o <> string " _"
  Outfix o p -> text o <> string " _ " <> text p


newtype ShowP = ShowP (Int -> String -> String)

instance Semigroup ShowP where
  a <> b = ShowP $ \ p -> showsPrec p a . showsPrec p b

instance Monoid ShowP where
  mempty = ShowP (const id)

instance Show ShowP where
  showsPrec p (ShowP f) = f p
