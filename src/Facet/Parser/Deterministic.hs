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
import qualified Data.CharSet as CharSet
import           Data.Foldable (find)
import           Data.Maybe (listToMaybe)
import           Facet.Parser.Combinators
import           Facet.Parser.Excerpt
import           Facet.Parser.Notice
import           Facet.Parser.Source
import           Facet.Parser.Span
import qualified Facet.Pretty as P
import           Prelude hiding (lookup, null)

parseString :: Maybe FilePath -> Parser a -> String -> ([Notice], a)
parseString path p s = first errs (parse p (sourceFromString path s) s)

parse :: Parser a -> Source -> String -> (State, a)
parse p ls s = runCont (choose p) (State ls s mempty (Pos 0 0)) mempty (,)

-- FIXME: some sort of trie might be smarter about common prefixes
data Parser a = Parser
  { null  :: Null a
  , table :: Table (Cont a)
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
        runCont k i (inFirstSet a <> follow) $ \ i' f' ->
        runCont (choose a) i' follow $ \ i'' a' ->
        let fa' = f' a' in fa' `seq` k' i'' fa'
      a' k = Cont $ \ i follow k' ->
        runCont k i follow $ \ i' a' ->
        let fa' = getNull (null f) i' a' in fa' `seq` k' i' fa'

instance Parsing Parser where
  position = Parser (Null pos) mempty

  char s = Parser (Insert (const s) (pure <$> inserted (show s))) (singleton s (Cont (\ i _ k' -> k' (advance i) s)))

  set s f e = Parser (Insert (const (f Nothing)) (pure <$> inserted e)) (Table [(s, Cont (\ i _ k' -> k' (advance i) (f (Just (head (input i))))))])

  source = Parser (Null src) mempty

  pl <|> pr = Parser (null pl <> null pr) (table pl <> table pr)

  fail a e = Parser (Insert (const a) (pure <$> inserted e)) mempty

  -- FIXME: accidentally capturing whitespace in p breaks things
  capture f p g = Parser (f <$> null p <*> null (g p)) (fmap go (table p))
    where
    go k = Cont $ \ i -> runCont (captureBody f g (\ (i', a) -> a <$ string (substring (src i) (Span (pos i) (pos i')))) k) i

  capture0 f p g = Parser (f <$> null p <*> null (g p)) (fmap go (table p))
    where
    go = captureBody f g (pure . snd)

inFirstSet :: Parser a -> Predicate
inFirstSet = memberOf . table

-- FIXME: this is probably exponential in the depth of the parse tree because of running g twice? but maybe laziness will save us?
-- FIXME: is this even correct?
-- FIXME: do we want to require that p be non-nullable?
captureBody :: (a -> b -> c) -> (Parser a' -> Parser b) -> ((State, a) -> Parser a') -> Cont a -> Cont c
captureBody f g mk k = Cont $ \ i follow k' ->
  let (i', a) = runCont k i (inFirstSet gp <> follow) (,)
      gp = g (mk (i', a))
  in runCont (choose gp) i' follow $ \ i'' b ->
  let fab = f a b in fab `seq` k' i'' fab


newtype Table a = Table { getTable :: [(CharSet.CharSet, a)] }
  deriving (Functor)

instance Semigroup (Table a) where
  -- NB: we append in reverse order because we want a right-biased union
  a1 <> a2 = Table (getTable a2 <> getTable a1)

instance Monoid (Table a) where
  mempty = Table mempty

singleton :: Char -> a -> Table a
singleton c k = Table [(CharSet.singleton c, k)]

member :: Char -> Table a -> Bool
member c = any (CharSet.member c . fst) . getTable

lookup :: Char -> Table a -> Maybe a
lookup c t = snd <$> find (CharSet.member c . fst) (getTable t)


newtype Predicate = Predicate { runPredicate :: Char -> Bool }

test :: Char -> Predicate -> Bool
test = flip runPredicate

instance Semigroup Predicate where
  p1 <> p2 = Predicate ((||) <$> runPredicate p1 <*> runPredicate p2)

instance Monoid Predicate where
  mempty = Predicate $ const False

memberOf :: Table a -> Predicate
memberOf = Predicate . flip member


newtype Cont a = Cont { runCont :: forall r . State -> Predicate -> (State -> a -> r) -> r }
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
  go = Cont $ \ i -> case listToMaybe (input i) >>= (`lookup` table p) of
    Nothing -> recovering go i (null p)
    Just k' -> runCont k' i

insertOrNull :: State -> Null a -> (State -> a -> r) -> r
insertOrNull i n k = case n of
  Null   a   -> k i (a i)
  Insert a e -> k i{ errs = errs i ++ e i } (a i)

recovering :: Cont a -> State -> Null a -> Predicate -> (State -> a -> r) -> r
recovering this i n follow = case input i of
  "" -> insertOrNull i n
  s:_
    -- FIXME: this choice is the only thing that depends on the follow set, & thus on the first set.
    -- we can eliminate it if we instead allow the continuation to decide, I *think*.
    -- might involve a recovery parameter to Cont, taking null p?
    | test s follow -> insertOrNull i n
    | otherwise     -> runCont this (advance i{ errs = errs i ++ [ deleted (show s) i ] }) follow


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
