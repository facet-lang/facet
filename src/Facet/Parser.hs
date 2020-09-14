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
, Null(..)
, First(..)
, Parser(..)
, Token(..)
, parse
, lexer
, parens
, braces
) where

import           Data.Coerce
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Set as Set

data Pos = Pos { line :: {-# UNPACK #-} !Int, col :: {-# unpack #-} !Int }
  deriving (Eq, Ord, Show)

data Span = Span { start :: {-# UNPACK #-} !Pos, end :: {-# unpack #-} !Pos }
  deriving (Eq, Ord, Show)

class (Ord s, Show s) => Symbol s where
  delta :: s -> Pos

class (Symbol s, Applicative p) => Parsing s p | p -> s where
  isNullable :: p a -> Bool
  firstSet :: p a -> Set.Set s
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


newtype Null s a = Null { getNullable :: Bool }
  deriving (Functor)

instance Applicative (Null s) where
  pure _ = Null True
  (<*>) = coerce (&&)

instance Symbol s => Parsing s (Null s) where
  isNullable = getNullable
  firstSet _ = Set.empty
  symbol _ = Null False
  (<|>) = coerce (||)
  _ <?> _ = Null False


data First s a = First
  { getNull  :: Null s a
  , getFirst :: Set.Set s
  }
  deriving (Functor)

instance Symbol s => Applicative (First s) where
  pure a = First (pure a) Set.empty
  First nf sf <*> ~(First na sa) = First (nf <*> na) (combine nf sf sa)

combine :: (Parsing s n, Semigroup t) => n a -> t -> t -> t
combine e s1 s2
  | isNullable e = s1 <> s2
  | otherwise    = s1

instance Symbol s => Parsing s (First s) where
  isNullable = isNullable . getNull
  firstSet = getFirst
  symbol s = First (symbol s) (Set.singleton s)
  First nl sl <|> First nr sr = First (nl <|> nr) (sl <> sr)
  First np sp <?> e = First (np <?> e) sp


data Parser s a = Parser
  { first     :: First s a
  , runParser :: [s] -> Set.Set s -> (a, [s])
  }
  deriving (Functor)

instance Symbol s => Applicative (Parser s) where
  pure a = Parser (pure a) (\ i _ -> (a, i))
  Parser ff kf <*> ~pa@(Parser fa ka) = Parser (ff <*> fa) $ \ i f ->
    let (f', i')  = kf i  (combine pa (getFirst fa) f)
        (a', i'') = ka i' f
        fa'       = f' a'
    in  fa' `seq` (fa', i'')

instance Symbol s => Parsing s (Parser s) where
  isNullable = isNullable . first
  firstSet = firstSet . first
  symbol s = Parser (symbol s) (\ i _ -> (s, tail i))
  pl <|> pr = Parser (first pl <|> first pr) $ \ i f -> case i of
    []
      | isNullable pl -> runParser pl [] f
      | isNullable pr -> runParser pr [] f
      | otherwise     -> error "unexpected eof"
    i@(s:_)
      | Set.member s (firstSet pl)    -> runParser pl i f
      | Set.member s (firstSet pr)    -> runParser pr i f
      | isNullable pl, Set.member s f -> runParser pl i f
      | isNullable pr, Set.member s f -> runParser pr i f
      | otherwise                     -> error ("illegal input symbol: " <> show s)
  p <?> (a, _) = p <|> pure a

parse :: Parser c a -> [c] -> a
parse p s = fst (runParser p s Set.empty)


data Token
  = LBrace
  | RBrace
  | LParen
  | RParen
  | Colon
  | Pipe
  | Arrow
  | Ident String -- FIXME: this is wrong
  deriving (Eq, Ord, Show)

lexer :: Parsing Char p => p Token
lexer
  =   LBrace <$ symbol '{'
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
