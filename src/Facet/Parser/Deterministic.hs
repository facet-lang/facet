{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
-- | A parser based on the design laid out in /Deterministic, Error-Correcting Combinator Parsers/, S. Doaitse Swierstra, Luc Duponcheel (tho it has diverged somewhat due both to changes in the language and our specific use case).
module Facet.Parser.Deterministic
( parseString
, parse
, Parser(..)
, Null(..)
) where

import           Data.Bifunctor (first)
import           Data.Foldable (find)
import           Data.Maybe (fromJust, listToMaybe)
import           Facet.Parser.Combinators
import           Facet.Parser.Excerpt
import           Facet.Parser.Notice
import           Facet.Parser.Source
import           Facet.Parser.Span
import qualified Facet.Pretty as P
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Terminal as ANSI
import           Prelude hiding (lookup, null)

parseString :: Maybe FilePath -> Parser a -> String -> ([Notice], Maybe a)
parseString path p s = first errs (parse p (sourceFromString path s) s)

parse :: Parser a -> Source -> String -> (State, Maybe a)
parse p ls s = runCont (choose p) (State ls s mempty (Pos 0 0)) mempty (,Nothing) (\ i a -> (i, Just a))

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
      f' k = Cont $ \ i follow err k' ->
        runCont k i (inFirstSet a <> follow) err $ \ i' f' ->
        runCont (choose a) i' follow err $ \ i'' a' ->
        let fa' = f' a' in fa' `seq` k' i'' fa'
      a' k = Cont $ \ i follow err k' ->
        runCont k i follow err $ \ i' a' ->
        let fa' = getNull (null f) i' a' in fa' `seq` k' i' fa'

instance Parsing Parser where
  position = Parser (Null pos) mempty

  -- FIXME: we can’t pick a sensible default for an arbitrary predicate; recovery should be smarter I think?
  satisfy p = Parser (Insert ((,) <$> err (P.pretty "inserted unknown character") <*> pure '_')) (Table [(Predicate p, Cont (\ i _ _ k' -> k' (advance i) (head (input i))))])

  source = Parser (Null src) mempty

  pl <|> pr = Parser (null pl <> null pr) (table pl <> table pr)

  fail a e = Parser (Insert ((,) <$> inserted e <*> pure a)) mempty

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
captureBody f g mk k = Cont $ \ i follow err k' ->
  let (i', a) = runCont k i (inFirstSet gp <> follow) (,Nothing) (\ i a -> (i, Just a))
      gp = g (mk (i', fromJust a))
  in runCont (choose gp) i' follow err $ \ i'' b ->
  let fab = f (fromJust a) b in fab `seq` k' i'' fab


newtype Table a = Table { getTable :: [(Predicate, a)] }
  deriving (Functor)

instance Semigroup (Table a) where
  -- NB: we append in reverse order because we want a right-biased union
  a1 <> a2 = Table (getTable a2 <> getTable a1)

instance Monoid (Table a) where
  mempty = Table mempty

member :: Char -> Table a -> Bool
member c = any (test c . fst) . getTable

lookup :: Char -> Table a -> Maybe a
lookup c t = snd <$> find (test c . fst) (getTable t)


newtype Predicate = Predicate { runPredicate :: Char -> Bool }

test :: Char -> Predicate -> Bool
test = flip runPredicate

instance Semigroup Predicate where
  p1 <> p2 = Predicate ((||) <$> runPredicate p1 <*> runPredicate p2)

instance Monoid Predicate where
  mempty = Predicate $ const False

memberOf :: Table a -> Predicate
memberOf = Predicate . flip member


newtype Cont a = Cont { runCont :: forall r . State -> Predicate -> (State -> r) -> (State -> a -> r) -> r }
  deriving (Functor)


data Null a
  = Null   (State -> a)
  | Insert (State -> ([Notice], a))
  deriving (Functor)

instance Semigroup (Null a) where
  l@Null{} <> _ = l
  _        <> r = r

instance Applicative Null where
  pure = Null . pure
  f <*> a = case f of
    Null   f    -> case a of
      Null   a -> Null   (f <*> a)
      Insert a -> Insert (\ i -> f i <$> a i)
    Insert f -> Insert (\ i -> let (fe, f') = f i in (combine (not (nullable a)) fe (getErrors a i), f' (getNull a i)))

nullable :: Null a -> Bool
nullable p = case p of
  Null  _  -> True
  Insert _ -> False

getNull :: Null a -> State -> a
getNull (Null   f) = f
getNull (Insert f) = snd . f

getErrors :: Null a -> State -> [Notice]
getErrors (Null   _) = const []
getErrors (Insert f) = fst . f

err :: PP.Doc ANSI.AnsiStyle -> State -> [Notice]
err d i = [Notice (Just Error) (stateExcerpt i) d []]

inserted :: String -> State -> [Notice]
inserted s = err (P.pretty "inserted" P.<+> P.pretty s)

deleted :: String -> State -> [Notice]
deleted  s = err (P.pretty "deleted"  P.<+> P.pretty s)

choose :: Parser a -> Cont a
choose p = go
  where
  go = Cont $ \ i -> case listToMaybe (input i) >>= (`lookup` table p) of
    Nothing -> recovering go i (null p)
    Just k' -> runCont k' i

insertOrNull :: State -> Null a -> (State -> r) -> (State -> a -> r) -> r
insertOrNull i n _ k = case n of
  Null   a -> k i (a i)
  Insert a -> let (e, a') = a i in k i{ errs = errs i ++ e } a'

recovering :: Cont a -> State -> Null a -> Predicate -> (State -> r) -> (State -> a -> r) -> r
recovering this i n follow = case input i of
  "" -> insertOrNull i n
  s:_
    | test s follow -> insertOrNull i n
    | otherwise     -> runCont this (advance i{ errs = errs i ++ deleted (show s) i }) follow


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
