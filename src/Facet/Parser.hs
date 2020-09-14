{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
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
, lexString
, parseString
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
import           Prelude hiding (lines, null, span)

data Pos = Pos { line :: {-# unpack #-} !Int, col :: {-# unpack #-} !Int, index :: {-# unpack #-} !Int }
  deriving (Eq, Ord, Show)

data Span = Span { start :: {-# unpack #-} !Pos, end :: {-# unpack #-} !Pos }
  deriving (Eq, Ord, Show)

instance Semigroup Span where
  Span s1 e1 <> Span s2 e2 = Span (min s1 s2) (max e1 e2)

class (Monoid set, Ord sym, Show sym) => Symbol set sym | sym -> set where
  singleton :: sym -> set
  member :: sym -> set -> Bool

instance Symbol CharSet.CharSet Char where
  singleton = CharSet.singleton
  member    = CharSet.member

class Applicative p => Parsing s p | p -> s where
  position :: p Pos
  source :: p Lines
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
  { null     :: Null s a
  , firstSet :: t
  , table    :: [(s, ParserCont t s a)]
  }
  deriving (Functor)

type ParserCont t s a = State s -> [t] -> (a, State s)

data State s = State
  { lines :: Lines
  , input :: [Token s]
  , errs  :: [String]
  , pos   :: {-# unpack #-} !Pos
  }

advance :: State sym -> State sym
advance (State s i es _) = State s (tail i) es (end (tokenSpan (head i)))


newtype Lines = Lines { getLines :: [String] }
  deriving (Eq, Ord, Show)

linesFromString :: String -> Lines
linesFromString = Lines . go
  where
  go = \case
    "" -> [""]
    s  -> let (line, rest) = takeLine s in line : either (const []) go rest
{-# inline linesFromString #-}

takeLine :: String -> (String, Either String String)
takeLine = go id where
  go line = \case
    ""        -> (line "", Left "")
    '\r':rest -> case rest of
      '\n':rest -> (line "\r\n", Right rest)
      _         -> (line "\r", Right rest)
    '\n':rest -> (line "\n", Right rest)
    c   :rest -> go (line . (c:)) rest
{-# inline takeLine #-}

(!) :: Lines -> Pos -> String
Lines lines ! pos = lines !! line pos
{-# INLINE (!) #-}

infixl 9 !


data Token sym = Token
  { tokenSymbol :: sym
  , tokenSource :: Maybe String -- ^ will be Nothing for tokens for which it would be constant
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
  source = Parser (Null lines) mempty []
  symbol s = Parser (Insert (const s) [ inserted s ]) (singleton s) [(s, \ i _ -> (s, advance i))]
  -- FIXME: warn on non-disjoint first sets
  pl <|> pr = Parser (null pl `alt` null pr) (firstSet pl <> firstSet pr) (table pl <> table pr)
  p <?> (a, e) = p <|> Parser (Insert (const a) [e]) mempty []

lexString :: Parser CharSet.CharSet Char a -> String -> ([String], a)
lexString p s = parse p (linesFromString s) (tokenize s)

parseString :: Symbol set sym => Parser CharSet.CharSet Char [Token sym] -> Parser set sym a -> String -> ([String], a)
parseString l p s = (el ++ ep, a)
  where
  lines = linesFromString s
  (el, ts) = parse l lines (tokenize s)
  (ep, a)  = parse p lines ts

parse :: Symbol set s => Parser set s a -> Lines -> [Token s] -> ([String], a)
parse p ls s = (errs i, a)
  where
  (a, i) = choose (null p) choices (State ls s mempty (Pos 0 0 0)) mempty
  choices = Map.fromList (table p)

tokenize :: String -> [Token Char]
tokenize = go (Pos 0 0 0)
  where
  go _ []     = []
  go p@(Pos l c i) (x:xs) = Token x Nothing (Span p p') : go p' xs
    where
    p' = case x of
      '\n' -> Pos (l + 1) 0       (i + 1)
      _    -> Pos l       (c + 1) (i + 1)


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
  member    = IntSet.member    . fromEnum


lexer :: Parsing Char p => p [Token Sym]
lexer = many
  $   Token LBrace Nothing <$> span (symbol '{')
  <|> Token RBrace Nothing <$> span (symbol '}')
  <|> Token LParen Nothing <$> span (symbol '(')
  <|> Token RParen Nothing <$> span (symbol ')')
  <|> Token Colon  Nothing <$> span (symbol ':')
  <|> Token Pipe   Nothing <$> span (symbol '|')
  <|> Token Arrow  Nothing <$> span (string "->")

parens :: Parsing Sym p => p a -> p a
parens a = symbol LParen *> a <* symbol RParen

braces :: Parsing Sym p => p a -> p a
braces a = symbol LBrace *> a <* symbol RBrace
