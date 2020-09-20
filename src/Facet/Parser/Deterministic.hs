{-# LANGUAGE DeriveFunctor #-}
module Facet.Parser.Deterministic
( Parser(..)
, Null(..)
, parseString
, parse
) where

import           Data.Bifunctor (first)
import           Data.CharSet (CharSet, member, singleton)
import qualified Data.Map as Map
import           Facet.Parser.Combinators
import           Facet.Parser.Excerpt
import           Facet.Parser.Notice
import           Facet.Parser.Source
import           Facet.Parser.Span
import           Prelude hiding (null)
import qualified Prettyprinter as P

instance Parsing Parser where
  position = Parser (Null pos) mempty []

  char s = Parser (Insert (const s) (pure <$> inserted (show s))) (singleton s) [ (s, \ i _ -> (advance i, s)) ]

  source = Parser (Null src) mempty []

  pl <|> pr = Parser (null pl `alt` null pr) (firstSet pl <> firstSet pr) (table pl <> table pr)

  fail a e = Parser (Insert (const a) (pure <$> inserted e)) mempty []

  -- FIXME: accidentally capturing whitespace in p breaks things
  capture f p g = Parser (f <$> null p <*> null (g p)) (firstSet p) (map (fmap go) (table p))
    where
    go k i = captureBody f g (\ (i', a) -> a <$ string (substring (src i) (Span (pos i) (pos i')))) k i

  capture0 f p g = Parser (f <$> null p <*> null (g p)) (firstSet p) (map (fmap go) (table p))
    where
    go = captureBody f g (pure . snd)

-- FIXME: this is probably exponential in the depth of the parse tree because of running g twice? but maybe laziness will save us?
-- FIXME: is this even correct?
-- FIXME: do we want to require that p be non-nullable?
captureBody f g mk k i follow =
  let (i', a) = k i (fs:follow)
      fs = firstSet gp
      gp = g (mk (i', a))
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
