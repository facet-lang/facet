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
import           Data.CharSet (CharSet, member, singleton)
import qualified Data.Map as Map
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
parse p ls s = runCont (choose p) (,) (State ls s mempty (Pos 0 0)) mempty

-- FIXME: some sort of trie might be smarter about common prefixes
data Parser a = Parser
  { null     :: Null a
  , firstSet :: CharSet
  , table    :: Table a
  }
  deriving (Functor)

instance Applicative Parser where
  pure a = Parser (pure a) mempty mempty
  f <*> a = Parser (null f <*> null a) (combine nullablef (firstSet f) (firstSet a)) tseq
    where
    nullablef = nullable (null f)
    tseq = combine nullablef tabf taba
      where
      tabf = fmap (\ k -> Cont $ \ k' i follow ->
        let (i', f')  = runCont k (,) i (firstSet a:follow)
            (i'', a') = runCont (choose a) (,) i' follow
            fa'       = f' a'
        in  fa' `seq` k' i'' fa') (table f)
      taba = fmap (\ k -> Cont $ \ k' i follow ->
        let (i', a') = runCont k (,) i follow
            fa'      = getNull (null f) i' a'
        in  fa' `seq` k' i' fa') (table a)

instance Parsing Parser where
  position = Parser (Null pos) mempty mempty

  char s = Parser (Insert (const s) (pure <$> inserted (show s))) (singleton s) (Map.singleton s (Cont (\ k' i _ -> k' (advance i) s)))

  source = Parser (Null src) mempty mempty

  -- NB: we append the tables in reverse order because <> on Map is left-biased and we want a right-biased union
  pl <|> pr = Parser (null pl <> null pr) (firstSet pl <> firstSet pr) (table pr <> table pl)

  fail a e = Parser (Insert (const a) (pure <$> inserted e)) mempty mempty

  -- FIXME: accidentally capturing whitespace in p breaks things
  capture f p g = Parser (f <$> null p <*> null (g p)) (firstSet p) (fmap go (table p))
    where
    go k = Cont $ \ k' i -> runCont (captureBody f g (\ (i', a) -> a <$ string (substring (src i) (Span (pos i) (pos i')))) k) k' i

  capture0 f p g = Parser (f <$> null p <*> null (g p)) (firstSet p) (fmap go (table p))
    where
    go = captureBody f g (pure . snd)

-- FIXME: this is probably exponential in the depth of the parse tree because of running g twice? but maybe laziness will save us?
-- FIXME: is this even correct?
-- FIXME: do we want to require that p be non-nullable?
captureBody :: (a -> b -> c) -> (Parser a' -> Parser b) -> ((State, a) -> Parser a') -> Cont a -> Cont c
captureBody f g mk k = Cont $ \ k' i follow ->
  let (i', a) = runCont k (,) i (fs:follow)
      fs = firstSet gp
      gp = g (mk (i', a))
      (i'', b) = runCont (choose gp) (,) i' follow
      fab = f a b
  in fab `seq` k' i'' fab


type Table a = Map.Map Char (Cont a)

newtype Cont a = Cont { runCont :: forall r . (State -> a -> r) -> State -> [CharSet] -> r }
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
choose p = Cont go
  where
  go k i follow = case input i of
    []  -> insertOrNull k (null p) i
    s:_ -> case Map.lookup s (table p) of
      Nothing
        | any (member s) follow -> insertOrNull k (null p) i
        | otherwise             -> runCont (choose p) k (advance i{ errs = errs i ++ [ deleted (show s) i ] }) follow
      Just k'                   -> runCont k' k i follow

insertOrNull :: (State -> a -> r) -> Null a -> State -> r
insertOrNull k n i = case n of
  Null   a   -> k i (a i)
  Insert a e -> k i{ errs = errs i ++ e i } (a i)


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
