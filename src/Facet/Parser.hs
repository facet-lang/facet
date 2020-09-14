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
, State(..)
, Sym(..)
, Token(..)
, parse
, tokenize
, lexer
, parens
, braces
) where

import qualified Data.CharSet as CharSet
import qualified Data.IntSet as IntSet
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import           Prelude hiding (null, span)

data Pos = Pos { line :: {-# UNPACK #-} !Int, col :: {-# unpack #-} !Int }
  deriving (Eq, Ord, Show)

instance Semigroup Pos where
  Pos l1 c1 <> Pos l2 c2 = Pos (l1 + l2) (c1 + c2)

instance Monoid Pos where
  mempty = Pos 0 0

data Span = Span { start :: {-# unpack #-} !Pos, end :: {-# unpack #-} !Pos }
  deriving (Eq, Ord, Show)

class (Monoid set, Ord sym, Show sym) => Symbol set sym | sym -> set where
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
  -- FIXME: always require <?> to terminate a chain of alternatives
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


data Null s a
  = Null   (State s -> a)
  | Insert (State s -> a) [String]
  deriving (Functor)

nullable :: Null s a -> Bool
nullable p = case p of
  Null  _    -> True
  Insert _ _ -> False

getNull :: Null s a -> State s -> a
getNull (Null   f)   = f
getNull (Insert f _) = f

getErrors :: Null s a -> [String]
getErrors (Null   _)   = []
getErrors (Insert _ e) = e

instance Applicative (Null s) where
  pure = Null . pure
  f <*> a = case f of
    Null   f    -> case a of
      Null   a    -> Null   (f <*> a)
      Insert a sa -> Insert (f <*> a) sa
    Insert f sf -> Insert (f <*> getNull a) (combine (not (nullable a)) sf (getErrors a))

inserted :: Show s => s -> String
inserted s = "inserted " <> show s

deleted :: Show s => s -> String
deleted s = "deleted " <> show s

alt :: Null s a -> Null s a -> Null s a
alt l@Null{} _ = l
alt _        r = r

choose :: Symbol set s => Null s a -> Map.Map s (ParserCont set s a) -> ParserCont set s a
choose p choices = go
  where
  go i noskip = case input i of
    []  -> insertOrNull p i
    s:_ -> let s' = tokenSymbol s in case Map.lookup s' choices of
      Nothing
        | any (member s') noskip -> insertOrNull p i
        | otherwise              -> choose p choices (advance i{ errs = errs i ++ [ deleted s' ] }) noskip
      Just k -> k i noskip

insertOrNull :: Null s a -> State s -> (a, State s)
insertOrNull n i = case n of
  Null   a   -> (a i, i)
  Insert a e -> (a i, i{ errs = errs i ++ e })

data Parser t s a = Parser
  { null  :: Null s a
  , first :: t
  , table :: [(s, ParserCont t s a)]
  }
  deriving (Functor)

type ParserCont t s a = State s -> [t] -> (a, State s)

data State s = State
  { input :: [Token s]
  , errs  :: [String]
  , pos   :: {-# unpack #-} !Pos
  }

advance :: State sym -> State sym
advance (State i es _) = State (tail i) es (end (tokenSpan (head i)))

data Token sym = Token
  { tokenSymbol :: sym
  , tokenSpan   :: Span
  }
  deriving (Show)

instance Symbol set sym => Applicative (Parser set sym) where
  pure a = Parser (pure a) mempty []
  Parser nf ff tf <*> ~(Parser na fa ta) = Parser (nf <*> na) (combine (nullable nf) ff fa) $ tseq tf ta
    where
    choices = Map.fromList ta
    tseq tf ta = combine (nullable nf) tabf taba
      where
      tabf = map (fmap (\ k i noskip ->
        let (f', i')  = k i (fa:noskip)
            (a', i'') = choose na choices i' noskip
            fa'       = f' a'
        in  fa' `seq` (fa', i''))) tf
      taba = map (fmap (\ k i noskip ->
        let (a', i') = k i noskip
            fa'      = getNull nf i' a'
        in  fa' `seq` (fa', i'))) ta

instance Symbol set sym => Parsing sym (Parser set sym) where
  position = Parser (Null pos) mempty []
  symbol s = Parser (Insert (const s) [ inserted s ]) (singleton s) [(s, \ i _ -> (s, advance i))]
  -- FIXME: warn on non-disjoint first sets
  pl <|> pr = Parser (null pl `alt` null pr) (first pl <> first pr) (table pl <> table pr)
  p <?> (a, e) = p <|> Parser (Insert (const a) [e]) mempty []

parse :: Symbol set s => Parser set s a -> [Token s] -> (a, [String])
parse p s = errs <$> choose (null p) choices (State s mempty mempty) mempty
  where
  choices = Map.fromList (table p)

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
