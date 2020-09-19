{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Parser
( Pos(..)
, Span(..)
, Parsing(..)
, (<?>)
, string
, set
, opt
, optional
, many
, chainr
, chainl
, chainr1
, chainl1
, sepBy
, sepBy1
, some
, span
, spanned
, Parser(..)
, State(..)
, Source(..)
, sourceFromString
, takeLine
, substring
, (!)
, Excerpt(..)
, excerpted
, Level(..)
, prettyLevel
, Notice(..)
, prettyNotice
, parseString
, parse
, parens
, braces
, brackets
, decl
, type'
, expr
) where

import           Control.Applicative (liftA2, (<**>))
import           Data.Bifunctor (first)
import           Data.CharSet (CharSet, fromList, member, singleton, toList)
import qualified Data.CharSet.Unicode as CharSet
import           Data.Foldable (traverse_)
import           Data.Functor.Identity
import           Data.List (isSuffixOf)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Facet.Functor.C
import qualified Facet.Syntax.Untyped.Lifted as S
import           Prelude hiding (fail, lines, null, span)
import qualified Prettyprinter as P
import           Prettyprinter.Render.Terminal as ANSI

data Pos = Pos { line :: {-# unpack #-} !Int, col :: {-# unpack #-} !Int }
  deriving (Eq, Ord, Show)

data Span = Span { start :: {-# unpack #-} !Pos, end :: {-# unpack #-} !Pos }
  deriving (Eq, Ord, Show)

instance Semigroup Span where
  Span s1 e1 <> Span s2 e2 = Span (min s1 s2) (max e1 e2)


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
  capture :: (a -> b -> c) -> p a -> (p a -> p b) -> p c

instance Parsing Parser where
  position = Parser (Null pos) mempty []

  char s = Parser (Insert (const s) (pure <$> inserted (show s))) (singleton s) [ (s, \ i _ -> (advance i, s)) ]

  source = Parser (Null src) mempty []

  pl <|> pr = Parser (null pl `alt` null pr) (firstSet pl <> firstSet pr) (table pl <> table pr)

  fail a e = Parser (Insert (const a) (pure <$> inserted e)) mempty []

  -- FIXME: this is probably exponential in the depth of the parse tree because of running g twice? but maybe laziness will save us?
  -- FIXME: is this even correct?
  -- FIXME: do we want to require that p be non-nullable?
  -- FIXME: accidentally capturing whitespace in p breaks things
  capture f p g = Parser (f <$> null p <*> null (g p)) (firstSet p) (map (fmap go) (table p))
    where
    go k i follow =
      let (i', a) = k i (fs:follow)
          s = substring (src i) (Span (pos i) (pos i'))
          fs = firstSet gp
          gp = g (a <$ string s)
          choices = Map.fromList (table gp)
          (i'', b) = choose (null gp) choices i' follow
          fab = f a b
      in fab `seq` (i'', fab)

instance (Parsing f, Applicative g) => Parsing (f :.: g) where
  position = C $ pure <$> position
  char s   = C $ pure <$> char s
  source   = C $ pure <$> source
  l <|> r  = C $ getC l <|> getC r
  fail a s = C $ fail (pure a) s
  capture f p g = C $ capture (liftA2 f) (getC p) (getC . g . C)

-- FIXME: always require <?>/fail to terminate a chain of alternatives
(<?>) :: Parsing p => p a -> (a, String) -> p a
p <?> (a, s) = p <|> fail a s
infixl 2 <?>

string :: Parsing p => String -> p String
string s = s <$ traverse_ char s <?> (s, s)

set :: Parsing p => CharSet -> (Maybe Char -> t) -> String -> p t
set t f s = foldr ((<|>) . fmap (f . Just) . char) (fail (f Nothing) s) (toList t)

opt :: Parsing p => p a -> a -> p a
opt p v = p <|> pure v

optional :: Parsing p => p a -> p (Maybe a)
optional p = opt (Just <$> p) Nothing

many :: Parsing p => p a -> p [a]
many p = go where go = opt ((:) <$> p <*> go) []

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


combine :: Semigroup t => Bool -> t -> t -> t
combine e s1 s2
  | e         = s1 <> s2
  | otherwise = s1


data Null a
  = Null   (State -> a)
  | Insert (State -> a) (State -> [Notice])
  deriving (Functor)

nullable :: Null a -> Bool
nullable p = case p of
  Null  _    -> True
  Insert _ _ -> False

getNull :: Null a -> State -> a
getNull (Null   f)   = f
getNull (Insert f _) = f

getErrors :: Null a -> State -> [Notice]
getErrors (Null   _)   = const []
getErrors (Insert _ f) = f

instance Applicative Null where
  pure = Null . pure
  f <*> a = case f of
    Null   f    -> case a of
      Null   a    -> Null   (f <*> a)
      Insert a sa -> Insert (f <*> a) sa
    Insert f sf -> Insert (f <*> getNull a) (combine (not (nullable a)) sf (getErrors a))

inserted :: String -> State -> Notice
inserted s i = Notice (Just Error) (stateExcerpt i) (P.pretty "inserted" P.<+> P.pretty s) []

deleted :: String -> State -> Notice
deleted  s i = Notice (Just Error) (stateExcerpt i) (P.pretty "deleted"  P.<+> P.pretty s) []

alt :: Null a -> Null a -> Null a
alt l@Null{} _ = l
alt _        r = r

choose :: Null a -> Map.Map Char (ParserCont a) -> ParserCont a
choose p choices = go
  where
  go i noskip = case input i of
    []  -> insertOrNull p i
    s:_ -> case Map.lookup s choices of
      Nothing
        | any (member s) noskip -> insertOrNull p i
        | otherwise             -> choose p choices (advance i{ errs = errs i ++ [ deleted (show s) i ] }) noskip
      Just k -> k i noskip

insertOrNull :: Null a -> State -> (State, a)
insertOrNull n i = case n of
  Null   a   -> (i, a i)
  Insert a e -> (i{ errs = errs i ++ e i }, a i)

data Parser a = Parser
  { null     :: Null a
  , firstSet :: CharSet
  , table    :: [(Char, ParserCont a)]
  }
  deriving (Functor)

type ParserCont a = State -> [CharSet] -> (State, a)

data State = State
  { src   :: Source
  , input :: String
  , errs  :: [Notice]
  , pos   :: {-# unpack #-} !Pos
  }

advance :: State -> State
advance (State s i es (Pos l c)) = State s (tail i) es $ case head i of
  '\n' -> Pos (l + 1) 0
  _    -> Pos l       (c + 1)


stateExcerpt :: State -> Excerpt
stateExcerpt i = Excerpt (path (src i)) (src i ! pos i) (Span (pos i) (pos i))


data Source = Source
  { path  :: Maybe FilePath
  , lines :: [String]
  }
  deriving (Eq, Ord, Show)

sourceFromString :: Maybe FilePath -> String -> Source
sourceFromString path = Source path . go
  where
  go = \case
    "" -> [""]
    s  -> let (line, rest) = takeLine s in line : either (const []) go rest
{-# inline sourceFromString #-}

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

substring :: Source -> Span -> String
substring source (Span (Pos sl sc) (Pos el ec)) = concat (onHead (drop sc) (onLast (take ec) (drop sl (take (el+1) (lines source)))))
  where
  onHead f = \case
    []   -> []
    x:xs -> f x : xs
  onLast f = go
    where
    go = \case
      []   -> []
      [x]  -> [f x]
      x:xs -> x:go xs

(!) :: Source -> Pos -> String
Source _ lines ! pos = lines !! line pos
{-# INLINE (!) #-}

infixl 9 !


data Excerpt = Excerpt
  { excerptPath :: !(Maybe FilePath)
  , excerptLine :: !String
  , excerptSpan :: {-# UNPACK #-} !Span
  }
  deriving (Eq, Ord, Show)

excerpted :: Parsing p => p a -> p (Excerpt, a)
excerpted p = first . mk <$> source <*> spanned p
  where
  mk src span = Excerpt (path src) (src ! start span) span


data Level
  = Warn
  | Error
  deriving (Eq, Ord, Show)

prettyLevel :: Level -> P.Doc AnsiStyle
prettyLevel = \case
  Warn  -> magenta (P.pretty "warning")
  Error -> red     (P.pretty "error")


data Notice = Notice
  { level   :: !(Maybe Level)
  , excerpt :: {-# UNPACK #-} !Excerpt
  , reason  :: !(P.Doc AnsiStyle)
  , context :: ![P.Doc AnsiStyle]
  }
  deriving (Show)

prettyNotice :: Notice -> P.Doc AnsiStyle
prettyNotice (Notice level (Excerpt path text span) reason context) = P.vsep
  ( P.nest 2 (P.group (P.fillSep
    [ bold (P.pretty (fromMaybe "(interactive)" path)) <> P.colon <> pos (start span) <> P.colon <> foldMap ((P.space <>) . (<> P.colon) . prettyLevel) level
    , reason
    ]))
  : blue (P.pretty (succ (line (start span)))) P.<+> P.align (P.vcat
    [ blue (P.pretty '|') P.<+> if "\n" `isSuffixOf` text then P.pretty (init text) <> blue (P.pretty "\\n") else P.pretty text <> blue (P.pretty "<end of input>")
    , blue (P.pretty '|') P.<+> padding span <> caret span
    ])
  : context)
  where
  pos (Pos l c) = bold (P.pretty (succ l)) <> P.colon <> bold (P.pretty (succ c))

  padding (Span (Pos _ c) _) = P.pretty (replicate c ' ')

  caret (Span start@(Pos sl sc) end@(Pos el ec))
    | start == end = green (P.pretty '^')
    | sl    == el  = green (P.pretty (replicate (ec - sc) '~'))
    | otherwise    = green (P.pretty "^…")

  bold = P.annotate ANSI.bold


red, green, blue, magenta :: P.Doc AnsiStyle -> P.Doc AnsiStyle
red     = P.annotate $ color Red
green   = P.annotate $ color Green
blue    = P.annotate $ color Blue
magenta = P.annotate $ color Magenta


instance Applicative Parser where
  pure a = Parser (pure a) mempty []
  Parser nf ff tf <*> ~(Parser na fa ta) = Parser (nf <*> na) (combine (nullable nf) ff fa) $ tseq tf ta
    where
    choices = Map.fromList ta
    tseq tf ta = combine (nullable nf) tabf taba
      where
      tabf = map (fmap (\ k i noskip ->
        let (i', f')  = k i (fa:noskip)
            (i'', a') = choose na choices i' noskip
            fa'       = f' a'
        in  fa' `seq` (i'', fa'))) tf
      taba = map (fmap (\ k i noskip ->
        let (i', a') = k i noskip
            fa'      = getNull nf i' a'
        in  fa' `seq` (i', fa'))) ta

parseString :: Maybe FilePath -> Parser a -> String -> ([Notice], a)
parseString path p s = first errs (parse p (sourceFromString path s) s)

parse :: Parser a -> Source -> String -> (State, a)
parse p ls s = choose (null p) choices (State ls s mempty (Pos 0 0)) mempty
  where
  choices = Map.fromList (table p)


lower' = fromList ['a'..'z']
lower, upper, letter, colon, comma, lparen, rparen, lbrace, rbrace, lbracket, rbracket :: Parsing p => p Char
lower = set lower' (fromMaybe 'a') "lowercase letter"
upper' = fromList ['A'..'Z']
upper = set upper' (fromMaybe 'A') "uppercase letter"
letter = lower <|> upper <?> ('a', "letter")
identS, ident, tident :: Parsing p => p Name
identS = (:) <$> lower <*> many letter
ident = token identS
tident = token ((:) <$> upper <*> many letter)
colon = token (char ':')
comma = token (char ',')
lparen = token (char '(')
rparen = token (char ')')
lbrace = token (char '{')
rbrace = token (char '}')
lbracket = token (char '[')
rbracket = token (char ']')
arrow :: Parsing p => p String
arrow = token (string "->")
ws :: Parsing p => p ()
ws = opt (c <* ws) ()
  where
  c = set wsSet (const ()) "whitespace"
  wsSet = CharSet.separator <> CharSet.control

token :: Parsing p => p a -> p a
token p = p <* ws

parens :: Parsing p => p a -> p a
parens a = lparen *> a <* rparen

braces :: Parsing p => p a -> p a
braces a = lbrace *> a <* rbrace

brackets :: Parsing p => p a -> p a
brackets a = lbracket *> a <* rbracket


type Name = String

-- case
-- : (x : a) -> (f : a -> b) -> b
-- { f x }

decl :: (S.Module expr ty decl mod, S.Err decl, S.Err ty, S.Err expr, Parsing p) => p mod
decl = (S..:) <$> ident <* colon <*> sig


sig :: (S.Decl expr ty decl, S.Err decl, S.Err ty, S.Err expr, Parsing p) => p decl
sig = runIdentity <$> getC (sig_ global tglobal)

sig_ :: forall p env expr ty decl . (Permutable env, Parsing p, S.Decl expr ty decl, S.Err decl, S.Err ty, S.Err expr) => (p :.: env) expr -> (p :.: env) ty -> (p :.: env) decl
sig_ var tvar = (S..=) <$> type_ tvar <*> expr_ var <|> bind var tvar <|> forAll (sig_ (weaken var)) tvar
  where
  bind :: forall env . Permutable env => (p :.: env) expr -> (p :.: env) ty -> (p :.: env) decl
  bind var tvar = lparen *> capture (const id) identS (\ i -> ws *> colon *> (type_ tvar S.>-> \ t -> rparen *> arrow *> sig_ (weaken var <|> liftCOuter t <* weaken (token i)) (weaken tvar)))

-- FIXME: bind multiple type variables of the same kind in a single set of braces
forAll :: (Permutable env, S.ForAll ty res, S.Type ty, S.Err ty, Parsing p) => (forall env' . Extends env env' => (p :.: env') ty -> (p :.: env') res) -> (p :.: env) ty -> (p :.: env) res
forAll k tvar = lbrace *> capture (const id) identS (\ i -> ws *> colon *> (type_ tvar S.>=> \ t -> rbrace *> arrow *> k (weaken tvar <|> liftCOuter t <* weaken (token i))))


type' :: (S.Decl expr ty decl, S.Err decl, S.Err ty, S.Err expr, Parsing p) => p decl
type' = runIdentity <$> getC (sig_ global tglobal)

type_ :: (Permutable env, S.Type ty, S.Err ty, Parsing p) => (p :.: env) ty -> (p :.: env) ty
type_ tvar = fn tvar <|> forAll type_ tvar <|> fail S.err "type"

fn :: (Permutable env, S.Type ty, S.Err ty, Parsing p) => (p :.: env) ty -> (p :.: env) ty
fn tvar = app tvar <**> opt (flip (S.-->) <$ arrow <*> fn tvar) id

app :: (Permutable env, S.Type ty, S.Err ty, Parsing p) => (p :.: env) ty -> (p :.: env) ty
app tvar = foldl (S..$) <$> atom tvar <*> many (atom tvar)

atom :: (Permutable env, S.Type ty, S.Err ty, Parsing p) => (p :.: env) ty -> (p :.: env) ty
atom tvar
  =   parens (prd <$> sepBy (type_ tvar) comma)
  <|> tvar
  <|> S._Type <$ string "Type"
  where
  prd [] = S._Unit
  prd ts = foldl1 (S..*) ts

tglobal :: (S.Type ty, Parsing p) => p ty
tglobal = S.tglobal <$> tident <?> (S.tglobal "_", "variable")


expr :: (S.Expr expr, S.Err expr, Parsing p) => p expr
expr = runIdentity <$> getC (expr_ global)

global :: (S.Expr expr, Parsing p) => p expr
global = S.global <$> ident <?> (S.global "_", "variable")

expr_ :: forall p env expr . (Permutable env, S.Expr expr, S.Err expr, Parsing p) => (p :.: env) expr -> (p :.: env) expr
expr_ var = foldl (S.$$) <$> atom_ var <*> many (atom_ var)
  where
  -- FIXME: patterns
  lam_ :: Permutable env' => (p :.: env') expr -> (p :.: env') expr
  lam_ var = braces $ clause_ var
  clause_ :: Permutable env' => (p :.: env') expr -> (p :.: env') expr
  clause_ var = S.lam0 (\ v -> capture (const id) identS (\ i -> let var' = weaken var <|> liftCOuter v <* token i in ws *> (clause_ var' <|> arrow *> expr_ var'))) <?> (S.err, "clause")
  atom_ var
    =   lam_ var
    <|> parens (prd <$> sepBy (expr_ var) comma)
    <|> var
    where
    prd [] = S.unit
    prd ts = foldl1 (S.**) ts
