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
, advance
, Token(..)
, parse
, lexer
, parens
, braces
) where

import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Set as Set

data Pos = Pos { line :: {-# UNPACK #-} !Int, col :: {-# unpack #-} !Int }
  deriving (Eq, Ord, Show)

instance Semigroup Pos where
  Pos l1 c1 <> Pos l2 c2 = Pos (l1 + l2) (c1 + c2)

instance Monoid Pos where
  mempty = Pos 0 0

data Span = Span { start :: {-# unpack #-} !Pos, end :: {-# unpack #-} !Pos }
  deriving (Eq, Ord, Show)

class (Ord s, Show s) => Symbol s where
  delta :: s -> Pos

instance Symbol Char where
  delta '\n' = Pos 1 0
  delta _    = Pos 0 1

class (Symbol s, Applicative p) => Parsing s p | p -> s where
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


data Parser s a = Parser
  { nullable  :: Bool
  , first     :: Set.Set s
  , runParser :: Input s -> Set.Set s -> (a, Input s)
  }
  deriving (Functor)

data Input s = Input
  { input :: ![s]
  , pos   :: {-# unpack #-} !Pos
  }

advance :: Symbol s => Input s -> s -> Input s
advance (Input i p) s = Input (tail i) (p <> delta s)

instance Symbol s => Applicative (Parser s) where
  pure a = Parser True Set.empty (\ i _ -> (a, i))
  Parser nf ff kf <*> ~(Parser na fa ka) = Parser (nf && na) (combine nf ff fa) $ \ i f ->
    let (f', i')  = kf i  (combine na fa f)
        (a', i'') = ka i' f
        fa'       = f' a'
    in  fa' `seq` (fa', i'')

instance Symbol s => Parsing s (Parser s) where
  symbol s = Parser False (Set.singleton s) (\ i _ -> (s, advance i s))
  pl <|> pr = Parser (nullable pl || nullable pr) (first pl <> first pr) $ \ i f -> case input i of
    []
      | nullable pl -> runParser pl i f
      | nullable pr -> runParser pr i f
      | otherwise   -> error "unexpected eof"
    s:_
      | Set.member s (first pl)     -> runParser pl i f
      | Set.member s (first pr)     -> runParser pr i f
      | nullable pl, Set.member s f -> runParser pl i f
      | nullable pr, Set.member s f -> runParser pr i f
      | otherwise                   -> error ("illegal input symbol: " <> show s)
  p <?> (a, _) = p <|> pure a

parse :: Parser c a -> [c] -> a
parse p s = fst (runParser p (Input s mempty) Set.empty)


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
