{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
module Facet.Parser.Deterministic
( parseString
, parseString'
, parse
, Parser(..)
, Null(..)
) where

import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Bifunctor (first)
import           Data.CharSet (CharSet, member, singleton)
import           Data.Foldable (traverse_)
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

-- FIXME: move this somewhere more reasonable for execution from ghci only.
parseString' :: P.Pretty a => MonadIO m => Parser a -> String -> m ()
parseString' p s = do
  let (errs, a) = parseString Nothing p s
  traverse_ (P.putDoc . prettyNotice) errs
  P.putDoc (P.pretty a)

parse :: Parser a -> Source -> String -> (State, a)
parse p ls s = runCont (choose (null p) choices) (State ls s mempty (Pos 0 0)) mempty
  where
  choices = buildMap (table p)

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
    choices = buildMap (table a)
    tseq = combine nullablef tabf taba
      where
      tabf = fmap (\ k -> cont $ \ i noskip ->
        let (i', f')  = runCont k i (firstSet a:noskip)
            (i'', a') = runCont (choose (null a) choices) i' noskip
            fa'       = f' a'
        in  fa' `seq` (i'', fa')) (table f)
      taba = fmap (\ k -> cont $ \ i noskip ->
        let (i', a') = runCont k i noskip
            fa'      = getNull (null f) i' a'
        in  fa' `seq` (i', fa')) (table a)

instance Parsing Parser where
  position = Parser (Null pos) mempty mempty

  char s = Parser (Insert (const s) (pure <$> inserted (show s))) (singleton s) (Map.singleton s (cont (\ i _ -> (advance i, s))))

  source = Parser (Null src) mempty mempty

  -- NB: we append the tables in reverse order because <> on Map is left-biased and we want a right-biased union
  pl <|> pr = Parser (null pl <> null pr) (firstSet pl <> firstSet pr) (table pr <> table pl)

  fail a e = Parser (Insert (const a) (pure <$> inserted e)) mempty mempty

  -- FIXME: accidentally capturing whitespace in p breaks things
  capture f p g = Parser (f <$> null p <*> null (g p)) (firstSet p) (fmap go (table p))
    where
    go k = cont $ \ i -> runCont (captureBody f g (\ (i', a) -> a <$ string (substring (src i) (Span (pos i) (pos i')))) k) i

  capture0 f p g = Parser (f <$> null p <*> null (g p)) (firstSet p) (fmap go (table p))
    where
    go = captureBody f g (pure . snd)

-- FIXME: this is probably exponential in the depth of the parse tree because of running g twice? but maybe laziness will save us?
-- FIXME: is this even correct?
-- FIXME: do we want to require that p be non-nullable?
captureBody :: (a -> b -> c) -> (Parser a' -> Parser b) -> ((State, a) -> Parser a') -> Cont a -> Cont c
captureBody f g mk k = cont $ \ i follow ->
  let (i', a) = runCont k i (fs:follow)
      fs = firstSet gp
      gp = g (mk (i', a))
      choices = buildMap (table gp)
      (i'', b) = runCont (choose (null gp) choices) i' follow
      fab = f a b
  in fab `seq` (i'', fab)


type Table a = Map.Map Char (Cont a)

newtype Cont a = Cont (forall r . (State -> a -> r) -> State -> [CharSet] -> r)
  deriving (Functor)

runCont :: Cont a -> State -> [CharSet] -> (State, a)
runCont (Cont c) = c (,)

cont :: (State -> [CharSet] -> (State, a)) -> Cont a
cont k = Cont $ \ r i f -> uncurry r (k i f)


type ContMap a = Map.Map Char (Cont a)


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

choose :: Null a -> ContMap a -> Cont a
choose p choices = cont go
  where
  go i noskip = case input i of
    []  -> insertOrNull p i
    s:_ -> case Map.lookup s choices of
      Nothing
        | any (member s) noskip -> insertOrNull p i
        | otherwise             -> runCont (choose p choices) (advance i{ errs = errs i ++ [ deleted (show s) i ] }) noskip
      Just k                    -> runCont k i noskip

insertOrNull :: Null a -> State -> (State, a)
insertOrNull n i = case n of
  Null   a   -> (i, a i)
  Insert a e -> (i{ errs = errs i ++ e i }, a i)


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
combine e s1 s2
  | e         = s1 <> s2
  | otherwise = s1


buildMap :: Table a -> ContMap a
buildMap = id
