{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Facet.Parser
( Parsing(..)
, Null(..)
, First(..)
, Parser(..)
) where

import           Data.Coerce
import qualified Data.Set as Set

class Applicative p => Parsing s p | p -> s where
  isNullable :: p a -> Bool
  symbol :: s -> p s
  (<|>) :: p a -> p a -> p a
  (<?>) :: p a -> (a, String) -> p a
  infixl 2 <?>


newtype Null s a = Null { getNullable :: Bool }
  deriving (Functor)

instance Applicative (Null s) where
  pure _ = Null True
  (<*>) = coerce (&&)

instance Parsing s (Null s) where
  isNullable = getNullable
  symbol _ = Null False
  (<|>) = coerce (||)
  _ <?> _ = Null False


data First s a = First
  { getNull  :: Null s a
  , getFirst :: Set.Set s
  }
  deriving (Functor)

instance Ord s => Applicative (First s) where
  pure a = First (pure a) Set.empty
  First nf sf <*> ~(First na sa) = First (nf <*> na) (combine nf sf sa)

combine :: (Parsing s n, Semigroup t) => n a -> t -> t -> t
combine e s1 s2
  | isNullable e = s1 <> s2
  | otherwise    = s1

instance Ord s => Parsing s (First s) where
  isNullable = isNullable . getNull
  symbol s = First (symbol s) (Set.singleton s)
  First nl sl <|> First nr sr = First (nl <|> nr) (sl <> sr)
  First np sp <?> e = First (np <?> e) sp


data Parser s a = Parser
  { first     :: First s a
  , runParser :: [s] -> Set.Set s -> (a, [s])
  }
  deriving (Functor)

instance (Ord s, Show s) => Applicative (Parser s) where
  pure a = Parser (pure a) (\ i _ -> (a, i))
  Parser ff kf <*> ~pa@(Parser fa ka) = Parser (ff <*> fa) $ \ i f ->
    let (f', i')  = kf i  (combine pa (getFirst fa) f)
        (a', i'') = ka i' f
        fa'       = f' a'
    in  fa' `seq` (fa', i'')

instance (Ord s, Show s) => Parsing s (Parser s) where
  isNullable = isNullable . first
  symbol s = Parser (symbol s) (\ i _ -> (s, tail i))
  pl@(Parser fl kl) <|> pr@(Parser fr kr) = Parser (fl <|> fr) $ \ i f -> case i of
    []
      | isNullable pl -> kl [] f
      | isNullable pr -> kr [] f
      | otherwise     -> error "unexpected eof"
    i@(s:_)
      | Set.member s (getFirst fl)    -> kl i f
      | Set.member s (getFirst fr)    -> kr i f
      | isNullable pl, Set.member s f -> kl i f
      | isNullable pr, Set.member s f -> kr i f
      | otherwise                     -> error ("illegal input symbol: " <> show s)
  p <?> (a, _) = p <|> pure a
