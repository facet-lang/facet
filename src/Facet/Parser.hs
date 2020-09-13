{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Facet.Parser
( Parsing(..)
, Nullable(..)
, First(..)
, ParserCont(..)
, Parser(..)
) where

import           Data.Coerce
import qualified Data.Set as Set

class Applicative p => Parsing s p | p -> s where
  symbol :: s -> p s
  (<|>) :: p a -> p a -> p a
  (<?>) :: p a -> (a, String) -> p a
  infixl 2 <?>

newtype Nullable s a = Nullable { getNullable :: Bool }
  deriving (Functor)

instance Applicative (Nullable s) where
  pure _ = Nullable True
  (<*>) = coerce (&&)

instance Parsing s (Nullable s) where
  symbol _ = Nullable False
  (<|>) = coerce (||)
  _ <?> _ = Nullable False


data First s a = First
  { isNullable :: Nullable s a
  , getFirst :: Set.Set s
  }
  deriving (Functor)

instance Ord s => Applicative (First s) where
  pure a = First (pure a) Set.empty
  First nf sf <*> ~(First na sa) = First (nf <*> na) (combine nf sf sa)

combine :: Semigroup t => Nullable s a -> t -> t -> t
combine e s1 s2
  | getNullable e = s1 <> s2
  | otherwise     = s1

instance Ord s => Parsing s (First s) where
  symbol s = First (symbol s) (Set.singleton s)
  First nl sl <|> First nr sr = First (nl <|> nr) (sl <> sr)
  First np sp <?> e = First (np <?> e) sp


newtype ParserCont s a = ParserCont { runParserCont :: [s] -> Set.Set s -> (a, [s]) }
  deriving (Functor)


data Parser s a = Parser
  { first     :: First s a
  , runParser :: [s] -> Set.Set s -> (a, [s])
  }
  deriving (Functor)

instance Ord s => Applicative (Parser s) where
  pure a = Parser (pure a) (\ i _ -> (a, i))
  Parser ff kf <*> ~(Parser fa ka) = Parser (ff <*> fa) (\ i f ->
    let (f', i')  = kf i  (combine (isNullable fa) (getFirst fa) f)
        (a', i'') = ka i' f
        fa'       = f' a'
    in  fa' `seq` (fa', i''))

instance (Ord s, Show s) => Parsing s (Parser s) where
  symbol s = Parser (symbol s) (\ i _ -> (s, tail i))
  Parser fl kl <|> Parser fr kr = Parser (fl <|> fr) $ \ i f -> case i of
    []
      | el        -> kl [] f
      | er        -> kr [] f
      | otherwise -> error "unexpected eof"
    i@(s:_)
      | Set.member s (getFirst fl)  -> kl i f
      | Set.member s (getFirst fr)  -> kr i f
      | el, Set.member s f          -> kl i f
      | er, Set.member s f          -> kr i f
      | otherwise                   -> error ("illegal input symbol: " <> show s)
    where
    el = getNullable (isNullable fl)
    er = getNullable (isNullable fr)
  p <?> (a, _) = p <|> pure a
