{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Parser
( Pos(..)
, Span(..)
, Parser(..)
, State(..)
, parseString
, parse
, parens
, braces
, brackets
, decl
, type'
, expr
) where

import           Control.Applicative ((<**>))
import           Data.Bifunctor (first)
import           Data.CharSet (CharSet, fromList, member, singleton)
import qualified Data.CharSet.Unicode as CharSet
import           Data.Functor.Identity
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Facet.Functor.C
import           Facet.Parser.Combinators
import           Facet.Parser.Excerpt
import           Facet.Parser.Notice
import           Facet.Parser.Source
import           Facet.Parser.Span
import qualified Facet.Syntax.Untyped.Lifted as S
import           Prelude hiding (fail, lines, null, span)
import qualified Prettyprinter as P

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
identS, ident, tidentS, tident :: Parsing p => p Name
identS = (:) <$> lower <*> many letter
ident = token identS
tidentS = (:) <$> upper <*> many letter
tident = token tidentS
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


type' :: (S.Type ty, S.Err ty, Parsing p) => p ty
type' = runIdentity <$> getC (type_ tglobal)

type_ :: (Permutable env, S.Type ty, S.Err ty, Parsing p) => (p :.: env) ty -> (p :.: env) ty
type_ tvar = fn tvar <|> forAll type_ tvar <|> fail S.err "type"

fn :: (Permutable env, S.Type ty, S.Err ty, Parsing p) => (p :.: env) ty -> (p :.: env) ty
fn tvar = app tatom tvar <**> opt (flip (S.-->) <$ arrow <*> fn tvar) id

tatom :: (Permutable env, S.Type ty, S.Err ty, Parsing p) => (p :.: env) ty -> (p :.: env) ty
tatom tvar
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
expr_ = app atom

-- FIXME: patterns
lam_ :: forall p env expr . (Permutable env, S.Expr expr, S.Err expr, Parsing p) => (p :.: env) expr -> (p :.: env) expr
lam_ var = braces $ clause_ var
  where
  clause_ :: Permutable env' => (p :.: env') expr -> (p :.: env') expr
  clause_ var = S.lam0 (\ v -> capture (const id) identS (\ i -> let var' = weaken var <|> liftCOuter v <* token i in ws *> (clause_ var' <|> arrow *> expr_ var'))) <?> (S.err, "clause")

atom :: (Permutable env, S.Expr expr, S.Err expr, Parsing p) => (p :.: env) expr -> (p :.: env) expr
atom var
  =   lam_ var
  <|> parens (prd <$> sepBy (expr_ var) comma)
  <|> var
  where
  prd [] = S.unit
  prd ts = foldl1 (S.**) ts

app :: (Permutable env, S.App expr, Parsing p) => ((p :.: env) expr -> (p :.: env) expr) -> ((p :.: env) expr -> (p :.: env) expr)
app atom tvar = foldl (S.$$) <$> atom tvar <*> many (atom tvar)
