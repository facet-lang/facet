{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Facet.Parser
( Pos(..)
, Span(..)
, Symbol(..)
, Parsing(..)
, string
, opt
, many
, some
, Parser(..)
, Input(..)
, Token(..)
, parse
, lexer
, parens
, braces
) where

import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.CharSet as CharSet

data Pos = Pos { line :: {-# UNPACK #-} !Int, col :: {-# unpack #-} !Int }
  deriving (Eq, Ord, Show)

instance Semigroup Pos where
  Pos l1 c1 <> Pos l2 c2 = Pos (l1 + l2) (c1 + c2)

instance Monoid Pos where
  mempty = Pos 0 0

data Span = Span { start :: {-# unpack #-} !Pos, end :: {-# unpack #-} !Pos }
  deriving (Eq, Ord, Show)

class (Monoid set, Show sym) => Symbol set sym | sym -> set where
  singleton :: sym -> set
  member :: sym -> set -> Bool
  advance :: Input sym -> sym -> Input sym

instance Symbol CharSet.CharSet Char where
  singleton = CharSet.singleton
  member = CharSet.member
  advance (Input i p) c = Input (tail i) $ p <> case c of
    '\n' -> Pos 1 0
    _    -> Pos 0 1

class Applicative p => Parsing s p | p -> s where
  symbol :: s -> p s
  (<|>) :: p a -> p a -> p a
  infixl 3 <|>
  (<?>) :: p a -> (a, String) -> p a
  infixl 2 <?>

string :: Parsing Char p => String -> p String
string s = foldr ((*>) . symbol) (pure s) s

opt :: Parsing s p => p a -> a -> p a
opt p v = p <|> pure v

many :: Parsing s p => p a -> p [a]
many p = opt ((:) <$> p <*> many p) []

some :: Parsing s p => p a -> p (NonEmpty a)
some p = (:|) <$> p <*> many p


combine :: Semigroup t => Bool -> t -> t -> t
combine e s1 s2
  | e         = s1 <> s2
  | otherwise = s1


data Parser t s a = Parser
  { nullable  :: Bool
  , first     :: t
  , runParser :: Input s -> t -> (a, Input s)
  }
  deriving (Functor)

data Input s = Input
  { input :: ![s]
  , pos   :: {-# unpack #-} !Pos
  }

instance Symbol set sym => Applicative (Parser set sym) where
  pure a = Parser True mempty (\ i _ -> (a, i))
  Parser nf ff kf <*> ~(Parser na fa ka) = Parser (nf && na) (combine nf ff fa) $ \ i f ->
    let (f', i')  = kf i  (combine na fa f)
        (a', i'') = ka i' f
        fa'       = f' a'
    in  fa' `seq` (fa', i'')

instance Symbol set sym => Parsing sym (Parser set sym) where
  symbol s = Parser False (singleton s) (\ i _ -> (s, advance i s))
  pl <|> pr = Parser (nullable pl || nullable pr) (first pl <> first pr) $ \ i f -> case input i of
    []
      | nullable pl -> runParser pl i f
      | nullable pr -> runParser pr i f
      | otherwise   -> error "unexpected eof"
    s:_
      | member s (first pl)     -> runParser pl i f
      | member s (first pr)     -> runParser pr i f
      | nullable pl, member s f -> runParser pl i f
      | nullable pr, member s f -> runParser pr i f
      | otherwise               -> error ("illegal input symbol: " <> show s)
  p <?> (a, _) = p <|> pure a

parse :: Monoid t => Parser t c a -> [c] -> a
parse p s = fst (runParser p (Input s mempty) mempty)


-- FIXME: we need to be able to associate spans with tokens

data Token
  = LBrace
  | RBrace
  | LParen
  | RParen
  | Colon
  | Pipe
  | Arrow
  | Ident
  deriving (Enum, Eq, Ord, Show)

lexer :: Parsing Char p => p [Token]
lexer = many
  $   LBrace <$ symbol '{'
  <|> RBrace <$ symbol '}'
  <|> LParen <$ symbol '('
  <|> RParen <$ symbol ')'
  <|> Colon  <$ symbol ':'
  <|> Pipe   <$ symbol '|'
  <|> Arrow  <$ string "->"

parens :: Parsing Token p => p a -> p a
parens a = symbol LParen *> a <* symbol RParen

braces :: Parsing Token p => p a -> p a
braces a = symbol LBrace *> a <* symbol RBrace
