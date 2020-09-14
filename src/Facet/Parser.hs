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
, Sym(..)
, Token(..)
, parse
, tokenize
, lexer
, parens
, braces
) where

import           Control.Applicative (liftA2)
import qualified Data.CharSet as CharSet
import qualified Data.IntSet as IntSet
import           Data.List.NonEmpty (NonEmpty(..))
import           Prelude hiding (null, span)

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

instance Symbol CharSet.CharSet Char where
  singleton = CharSet.singleton
  member = CharSet.member

class Applicative p => Parsing s p | p -> s where
  position :: p Pos
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

span :: Parsing s p => p a -> p Span
span p = Span <$> position <* p <*> position


combine :: Semigroup t => Bool -> t -> t -> t
combine e s1 s2
  | e         = s1 <> s2
  | otherwise = s1


data Null a
  = Null   a
  | Insert a [String]
  deriving (Functor)

instance Applicative Null where
  pure = Null
  f <*> a = case f of
    Null   f    -> fmap f a
    Insert f sf -> case a of
      Null   a    -> Insert (f a) sf
      Insert a sa -> Insert (f a) (sf <> sa)

alt :: Null a -> Null a -> Null a
alt l@Null{} _ = l
alt _        r = r

data Parser t s a = Parser
  { null      :: Null (Input s -> a)
  , first     :: t
  , runParser :: Input s -> t -> (a, Input s)
  }
  deriving (Functor)

nullable :: Parser t s a -> Bool
nullable p = case null p of
  Null  _    -> True
  Insert _ _ -> False

data Input s = Input
  { input :: ![Token s]
  , pos   :: {-# unpack #-} !Pos
  }

advance :: Input sym -> Input sym
advance (Input i _) = Input (tail i) (end (tokenSpan (head i)))

data Token sym = Token
  { tokenSymbol :: sym
  , tokenSpan   :: Span
  }
  deriving (Show)

instance Symbol set sym => Applicative (Parser set sym) where
  pure a = Parser (pure (pure a)) mempty (\ i _ -> (a, i))
  pf@(Parser nf ff kf) <*> ~pa@(Parser na fa ka) = Parser (liftA2 (<*>) nf na) (combine (nullable pf) ff fa) $ \ i f ->
    let (f', i')  = kf i  (combine (nullable pa) fa f)
        (a', i'') = ka i' f
        fa'       = f' a'
    in  fa' `seq` (fa', i'')

instance Symbol set sym => Parsing sym (Parser set sym) where
  position = Parser (pure pos) mempty $ \ i _ -> (pos i, i)
  symbol s = Parser (Insert (const s) [ "inserted " <> show s ]) (singleton s) (\ i _ -> (s, advance i))
  pl <|> pr = Parser (null pl `alt` null pr) (first pl <> first pr) $ \ i f -> case input i of
    []
      | nullable pl -> runParser pl i f
      | nullable pr -> runParser pr i f
      | otherwise   -> error "unexpected eof"
    Token s _:_
      | member s (first pl)     -> runParser pl i f
      | member s (first pr)     -> runParser pr i f
      | nullable pl, member s f -> runParser pl i f
      | nullable pr, member s f -> runParser pr i f
      | otherwise               -> error ("illegal input symbol: " <> show s)
  p <?> (a, _) = p <|> pure a

parse :: Monoid t => Parser t c a -> [Token c] -> a
parse p s = fst (runParser p (Input s mempty) mempty)

tokenize :: String -> [Token Char]
tokenize = go mempty
  where
  go _ []     = []
  go p (c:cs) = Token c (Span p p') : go p' cs
    where
    p' = p <> case c of
      '\n' -> Pos 1 0
      _    -> Pos 0 1


data Sym
  = LBrace
  | RBrace
  | LParen
  | RParen
  | Colon
  | Pipe
  | Arrow
  | Ident
  deriving (Enum, Eq, Ord, Show)

instance Symbol IntSet.IntSet Sym where
  singleton = IntSet.singleton . fromEnum
  member = IntSet.member . fromEnum


lexer :: Parsing Char p => p [Token Sym]
lexer = many
  $   Token LBrace <$> span (symbol '{')
  <|> Token RBrace <$> span (symbol '}')
  <|> Token LParen <$> span (symbol '(')
  <|> Token RParen <$> span (symbol ')')
  <|> Token Colon  <$> span (symbol ':')
  <|> Token Pipe   <$> span (symbol '|')
  <|> Token Arrow  <$> span (string "->")

parens :: Parsing Sym p => p a -> p a
parens a = symbol LParen *> a <* symbol RParen

braces :: Parsing Sym p => p a -> p a
braces a = symbol LBrace *> a <* symbol RBrace
