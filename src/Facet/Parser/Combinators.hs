{-# LANGUAGE TypeOperators #-}
module Facet.Parser.Combinators
( Parsing(..)
, (<?>)
, string
, set
, opt
, optional
, many
, skipMany
, skipSome
, chainr
, chainl
, chainr1
, chainl1
, sepBy
, sepBy1
, some
, span
, spanned
, parens
, braces
, brackets
, token
, ws
  -- * Character parsers
, lower
, upper
, letter
, colon
, comma
, lparen
, rparen
, lbrace
, rbrace
, lbracket
, rbracket
) where

import           Control.Applicative (liftA2, (<**>))
import qualified Data.CharSet as CharSet
import qualified Data.CharSet.Unicode as CharSet
import           Data.Foldable (traverse_)
import           Data.Maybe (fromMaybe)
import           Facet.Functor.C
import           Facet.Parser.Source
import           Facet.Parser.Span
import           Prelude hiding (fail, span)

class Applicative p => Parsing p where
  position :: p Pos
  char :: Char -> p Char
  source :: p Source
  -- FIXME: warn on non-disjoint first sets
  (<|>) :: p a -> p a -> p a
  infixl 3 <|>
  -- FIXME: allow failure values to produce errors from the state
  fail :: a -> String -> p a

  -- | Parse some text, and then parse something else constructed using a parser that parses the same literal text.
  --
  -- This is like a restricted form of the monadic bind.
  --
  -- FIXME: this is a bad name.
  capture :: (a -> b -> c) -> p a -> (p a -> p b) -> p c

  -- | Like capture, but the higher-order parser receives a pure parser instead of a parser of the same text.
  --
  -- FIXME: this is a bad name.
  capture0 :: (a -> b -> c) -> p a -> (p a -> p b) -> p c

instance (Parsing f, Applicative g) => Parsing (f :.: g) where
  position = C $ pure <$> position
  char s   = C $ pure <$> char s
  source   = C $ pure <$> source
  l <|> r  = C $ getC l <|> getC r
  fail a s = C $ fail (pure a) s
  capture f p g = C $ capture (liftA2 f) (getC p) (getC . g . C)
  capture0 f p g = C $ capture0 (liftA2 f) (getC p) (getC . g . C)

-- FIXME: always require <?>/fail to terminate a chain of alternatives
(<?>) :: Parsing p => p a -> (a, String) -> p a
p <?> (a, s) = p <|> fail a s
infixl 2 <?>

string :: Parsing p => String -> p String
string s = s <$ traverse_ char s <?> (s, s)

set :: Parsing p => CharSet.CharSet -> (Maybe Char -> t) -> String -> p t
set t f s = foldr ((<|>) . fmap (f . Just) . char) (fail (f Nothing) s) (CharSet.toList t)

opt :: Parsing p => p a -> a -> p a
opt p v = p <|> pure v

optional :: Parsing p => p a -> p (Maybe a)
optional p = opt (Just <$> p) Nothing

many :: Parsing p => p a -> p [a]
many p = go where go = opt ((:) <$> p <*> go) []

skipMany :: Parsing p => p a -> p ()
skipMany p = go where go = opt (p *> go) ()

skipSome :: Parsing p => p a -> p ()
skipSome p = p *> skipMany p

chainr :: Parsing p => p a -> p (a -> a -> a) -> a -> p a
chainr p = opt . chainr1 p

chainl :: Parsing p => p a -> p (a -> a -> a) -> a -> p a
chainl p = opt . chainl1 p

chainl1 :: Parsing p => p a -> p (a -> a -> a) -> p a
chainl1 p op = p <**> go
  where
  go = opt ((\ f y g x -> g (f x y)) <$> op <*> p <*> go) id

chainr1 :: Parsing p => p a -> p (a -> a -> a) -> p a
chainr1 p op = go
  where
  go = p <**> opt (flip <$> op <*> go) id

sepBy :: Parsing p => p a -> p s -> p [a]
sepBy p s = opt (sepBy1 p s) []

sepBy1 :: Parsing p => p a -> p s -> p [a]
sepBy1 p s = (:) <$> p <*> many (s *> p)

some :: Parsing p => p a -> p [a]
some p = (:) <$> p <*> many p

span :: Parsing p => p a -> p Span
span p = Span <$> position <* p <*> position

spanned :: Parsing p => p a -> p (Span, a)
spanned p = mk <$> position <*> p <*> position
  where
  mk s a e = (Span s e, a)


parens :: Parsing p => p a -> p a
parens a = lparen *> a <* rparen

braces :: Parsing p => p a -> p a
braces a = lbrace *> a <* rbrace

brackets :: Parsing p => p a -> p a
brackets a = lbracket *> a <* rbracket


token :: Parsing p => p a -> p a
token p = p <* ws


-- Character parsers

lowerSet, upperSet :: CharSet.CharSet
lowerSet = CharSet.fromList ['a'..'z']
upperSet = CharSet.fromList ['A'..'Z']

lower, upper, letter :: Parsing p => p Char
lower = set lowerSet (fromMaybe 'a') "lowercase letter"
upper = set upperSet (fromMaybe 'A') "uppercase letter"
letter = lower <|> upper <?> ('a', "letter")

colon, comma :: Parsing p => p Char
colon = token (char ':')
comma = token (char ',')

lparen, rparen :: Parsing p => p Char
lparen = token (char '(')
rparen = token (char ')')

lbrace, rbrace :: Parsing p => p Char
lbrace = token (char '{')
rbrace = token (char '}')

lbracket, rbracket :: Parsing p => p Char
lbracket = token (char '[')
rbracket = token (char ']')

ws :: Parsing p => p ()
ws = skipMany c
  where
  c = set wsSet (const ()) "whitespace"
  wsSet = CharSet.separator <> CharSet.control
