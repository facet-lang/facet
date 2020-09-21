{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
-- | A parser based on the design laid out in /Deterministic, Error-Correcting Combinator Parsers/, S. Doaitse Swierstra, Luc Duponcheel (tho it has diverged somewhat due both to changes in the language and our specific use case).
module Facet.Parser.Deterministic
( parseString
, parse
, Parser(..)
, Null(..)
) where

import           Data.Bifunctor (first)
import           Data.CharSet (CharSet, fromList, member)
import qualified Data.Map as Map
import           Data.Maybe (listToMaybe)
import           Facet.Parser.Combinators
import           Facet.Parser.Excerpt
import           Facet.Parser.Notice
import           Facet.Parser.Source
import           Facet.Parser.Span
import qualified Facet.Pretty as P
import           Prelude hiding (null)

parseString :: Maybe FilePath -> Parser a -> String -> ([Notice], a)
parseString path p s = first errs (parse p (sourceFromString path s) s)

parse :: Parser a -> Source -> String -> (State, a)
parse p ls s = runCont (choose p) (State ls s mempty (Pos 0 0)) mempty (,)

-- FIXME: some sort of trie might be smarter about common prefixes
data Parser a = Parser
  { null     :: Null a
  , table    :: Table a
  }
  deriving (Functor)

instance Applicative Parser where
  pure a = Parser (pure a) mempty
  f <*> a = Parser (null f <*> null a) tseq
    where
    nullablef = nullable (null f)
    tseq = combine nullablef (f' <$> table f) (a' <$> table a)
      where
      f' k = Cont $ \ i follow k' ->
        runCont k i (firstSet a:follow) $ \ i' f' ->
        runCont (choose a) i' follow $ \ i'' a' ->
        let fa' = f' a' in fa' `seq` k' i'' fa'
      a' k = Cont $ \ i follow k' ->
        runCont k i follow $ \ i' a' ->
        let fa' = getNull (null f) i' a' in fa' `seq` k' i' fa'

instance Parsing Parser where
  position = Parser (Null pos) mempty

  char s = Parser (Insert (const s) (pure <$> inserted (show s))) (Map.singleton s (Cont (\ i _ k' -> k' (advance i) s)))

  source = Parser (Null src) mempty

  -- NB: we append the tables in reverse order because <> on Map is left-biased and we want a right-biased union
  pl <|> pr = Parser (null pl <> null pr) (table pr <> table pl)

  fail a e = Parser (Insert (const a) (pure <$> inserted e)) mempty

  -- FIXME: accidentally capturing whitespace in p breaks things
  capture f p g = Parser (f <$> null p <*> null (g p)) (fmap go (table p))
    where
    go k = Cont $ \ i -> runCont (captureBody f g (\ (i', a) -> a <$ string (substring (src i) (Span (pos i) (pos i')))) k) i

  capture0 f p g = Parser (f <$> null p <*> null (g p)) (fmap go (table p))
    where
    go = captureBody f g (pure . snd)

firstSet :: Parser a -> CharSet
firstSet p = fromList $ Map.keys (table p)

-- FIXME: this is probably exponential in the depth of the parse tree because of running g twice? but maybe laziness will save us?
-- FIXME: is this even correct?
-- FIXME: do we want to require that p be non-nullable?
captureBody :: (a -> b -> c) -> (Parser a' -> Parser b) -> ((State, a) -> Parser a') -> Cont a -> Cont c
captureBody f g mk k = Cont $ \ i follow k' ->
  let (i', a) = runCont k i (fs:follow) (,)
      fs = firstSet gp
      gp = g (mk (i', a))
  in runCont (choose gp) i' follow $ \ i'' b ->
  let fab = f a b in fab `seq` k' i'' fab


type Table a = Map.Map Char (Cont a)

newtype Cont a = Cont { runCont :: forall r . State -> [CharSet] -> (State -> a -> r) -> r }
  deriving (Functor)


data Null a
  = Null   (State -> a)
  | Insert (State -> a) (State -> [Notice])
  deriving (Functor)

instance Semigroup (Null a) where
  l@Null{} <> _ = l
  _        <> r = r

instance Applicative Null where
  pure = Null . pure
  f <*> a = case f of
    Null   f    -> case a of
      Null   a    -> Null   (f <*> a)
      Insert a sa -> Insert (f <*> a) sa
    Insert f sf -> Insert (f <*> getNull a) (combine (not (nullable a)) sf (getErrors a))

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

inserted :: String -> State -> Notice
inserted s i = Notice (Just Error) (stateExcerpt i) (P.pretty "inserted" P.<+> P.pretty s) []

deleted :: String -> State -> Notice
deleted  s i = Notice (Just Error) (stateExcerpt i) (P.pretty "deleted"  P.<+> P.pretty s) []

choose :: Parser a -> Cont a
choose p = go
  where
  go = Cont $ \ i -> case listToMaybe (input i) >>= (`Map.lookup` table p) of
    Nothing -> \ follow -> recovering (`canMatch` follow) go i (null p) follow
    Just k' -> runCont k' i

insertOrNull :: State -> Null a -> (State -> a -> r) -> r
insertOrNull i n k = case n of
  Null   a   -> k i (a i)
  Insert a e -> k i{ errs = errs i ++ e i } (a i)

recovering :: (Char -> Bool) -> Cont a -> State -> Null a -> [CharSet] -> (State -> a -> r) -> r
recovering canMatch this i n follow k = case input i of
  "" -> insertOrNull i n k
  s:_
    -- FIXME: this choice is the only thing that depends on the follow set, & thus on the first set.
    -- we can eliminate it if we instead allow the continuation to decide, I *think*.
    -- might involve a recovery parameter to Cont, taking null p?
    | canMatch s -> insertOrNull i n k
    | otherwise  -> runCont this (advance i{ errs = errs i ++ [ deleted (show s) i ] }) follow k

canMatch :: Char -> [CharSet] -> Bool
canMatch = any . member


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


combine :: Semigroup t => Bool -> t -> t -> t
combine e
  | e         = (<>)
  | otherwise = const
