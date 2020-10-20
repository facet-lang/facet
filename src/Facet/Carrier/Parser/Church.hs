{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Carrier.Parser.Church
( -- * Parser carrier
  runParserWithString
, runParserWithFile
, runParserWithSource
, runParser
, ParserC(ParserC)
, emptyWith
, cutfailWith
, Input(..)
, pos_
, str_
, Err(..)
, input_
, reason_
, expected_
  -- * Parser effect
, module Facet.Effect.Parser
  -- * Cut effect
, module Control.Effect.Cut
) where

import Control.Algebra
import Control.Effect.Cut
import Control.Effect.NonDet
import Control.Effect.Throw
import Control.Lens (Lens', lens, (%~), (&), (.~))
import Control.Monad (ap)
import Control.Monad.Fail as Fail
import Control.Monad.Fix
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Data.Coerce (coerce)
import Data.Functor.Compose
import Data.Functor.Identity
import Data.List.NonEmpty (NonEmpty(..))
import Data.Set (Set, singleton)
import Facet.Effect.Parser
import Facet.Source as Source
import Facet.Span as Span
import Text.Parser.Char (CharParsing(..))
import Text.Parser.Combinators
import Text.Parser.Token (TokenParsing)

runParserWithString :: Has (Throw (Source, Err)) sig m => Int -> String -> ParserC m a -> m a
runParserWithString line = runParserWithSource . sourceFromString Nothing line
{-# INLINE runParserWithString #-}

runParserWithFile :: (Has (Throw (Source, Err)) sig m, MonadIO m) => FilePath -> ParserC m a -> m a
runParserWithFile path p = do
  src <- liftIO (readSourceFromFile path)
  runParserWithSource src p
{-# INLINE runParserWithFile #-}

runParserWithSource :: Has (Throw (Source, Err)) sig m => Source -> ParserC m a -> m a
runParserWithSource src@(Source _ _ _ (Line line _ _:|_)) = runParser (const pure) failure failure input
  where
  input = Input (Pos line 0) (contents src)
  failure = throwError . (,) src
{-# INLINE runParserWithSource #-}

runParser
  :: (Input -> a -> m r)
  -> (Err -> m r)
  -> (Err -> m r)
  -> Input
  -> ParserC m a
  -> m r
runParser leaf nil fail input (ParserC run) = run leaf nil fail input
{-# INLINE runParser #-}


newtype ParserC m a = ParserC
  { runParserC
    :: forall r
    .  (Input -> a -> m r) -- success
    -> (Err -> m r)        -- empty
    -> (Err -> m r)        -- cut
    -> Input
    -> m r
  }
  deriving (Functor)

instance Applicative (ParserC m) where
  pure a = ParserC (\ leaf _ _ input -> leaf input a)
  {-# INLINE pure #-}

  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Alternative (ParserC m) where
  empty = emptyWith Nothing mempty
  {-# INLINE empty #-}

  ParserC l <|> ParserC r = ParserC $ \ leaf nil fail i ->
    l
      leaf
      (\ el -> r
        leaf
        (nil  . extend el)
        (fail . extend el)
        i)
      fail
      i
    where
    extend el er = er & reason_ %~ (<|> reason el) & expected_ %~ (expected el <>)
  {-# INLINE (<|>) #-}

instance Monad (ParserC m) where
  ParserC m >>= f = ParserC $ \ leaf nil fail i -> m
    (\ i' -> runParser leaf (if pos i == pos i' then nil else fail) fail i' . f)
    nil
    fail
    i
  {-# INLINE (>>=) #-}

instance Algebra sig m => Fail.MonadFail (ParserC m) where
  fail = unexpected
  {-# INLINE fail #-}

instance MonadFix m => MonadFix (ParserC m) where
  mfix f = ParserC $ \ leaf nil fail input ->
    mfix (distParser input . f . run . fromParser input . snd)
    >>= run . uncurry (runParser (fmap pure . leaf) (pure . nil) (pure . fail))
    where
    fromParser = runParser (const pure) (error "mfix ParserC: empty") (error "mfix ParserC: cutfail")
  {-# INLINE mfix #-}

instance MonadIO m => MonadIO (ParserC m) where
  liftIO = lift . liftIO
  {-# INLINE liftIO #-}

instance MonadPlus (ParserC m)

instance MonadTrans ParserC where
  lift m = ParserC $ \ leaf _ _ input -> m >>= leaf input
  {-# INLINE lift #-}

instance Parsing (ParserC m) where
  try m = ParserC $ \ leaf nil _ input -> runParser leaf nil nil input m
  {-# INLINE try #-}

  eof = notFollowedBy anyChar <?> "end of input"
  {-# INLINE eof #-}

  unexpected s = ParserC $ \ _ nil _ input -> nil (Err input (Just s) mempty)
  {-# INLINE unexpected #-}

  m <?> s = ParserC $ \ leaf nil fail -> runParserC m
    leaf
    (nil . (expected_ .~ singleton s))
    fail
  {-# INLINE (<?>) #-}

  notFollowedBy p = ParserC $ \ leaf nil _ input -> runParserC p
    (\ _ a -> nil (Err input (Just (show a)) mempty))
    (\ _ -> leaf input ())
    (\ _ -> leaf input ())
    input
  {-# INLINE notFollowedBy #-}

instance CharParsing (ParserC m) where
  satisfy p = acceptC (\ c -> if p c then Just c else Nothing)
  {-# INLINE satisfy #-}

instance TokenParsing (ParserC m)

acceptC :: (Char -> Maybe a) -> ParserC m a
acceptC p = ParserC $ \ leaf nil _ input -> case str input of
  c:_ | Just a <- p c -> leaf (advance input) a
      | otherwise     -> nil (Err input (Just ("unexpected " <> show c)) mempty)
  _                   -> nil (Err input (Just "unexpected end of input") mempty)
{-# INLINE acceptC #-}

instance Algebra sig m => Algebra (Parser :+: Cut :+: NonDet :+: sig) (ParserC m) where
  alg hdl sig ctx = case sig of
    L (Accept p)         -> (<$ ctx) <$> acceptC p

    L (Label m s)        -> hdl (m <$ ctx) <?> s

    L (Unexpected s)     -> unexpected s

    L Position           -> ParserC $ \ leaf _ _ input -> leaf input (pos input <$ ctx)

    R (L Cutfail)        -> ParserC $ \ _ _ fail input -> fail (Err input Nothing mempty)

    R (L (Call m))       -> try (hdl (m <$ ctx))

    R (R (L (L Empty)))  -> empty

    R (R (L (R Choose))) -> pure (True <$ ctx) <|> pure (False <$ ctx)

    R (R (R other))      -> ParserC $ \ leaf nil fail input ->
      thread (fmap Compose . uncurry dst . getCompose ~<~ hdl) other (Compose (input, pure ctx))
      >>= runIdentity . uncurry (runParser (coerce leaf) (coerce nil) (coerce fail)) . getCompose
    where
    dst :: Applicative m => Input -> ParserC Identity (ParserC m a) -> m (Input, ParserC Identity a)
    dst = fmap runIdentity
        . runParser
          (\ i -> pure . distParser i)
          (pure . emptyk)
          (pure . cutfailk)
  {-# INLINE alg #-}

distParser :: Applicative m => Input -> ParserC m a -> m (Input, ParserC Identity a)
distParser = runParser purek emptyk cutfailk
{-# INLINE distParser #-}

purek :: Applicative m => Input -> a -> m (Input, ParserC n a)
purek    i a = pure (i, pure a)
{-# INLINE purek #-}

emptyk :: Applicative m => Err -> m (Input, ParserC n a)
emptyk   Err{ input, reason, expected } = pure (input, emptyWith   reason expected)
{-# INLINE emptyk #-}

cutfailk :: Applicative m => Err -> m (Input, ParserC n a)
cutfailk Err{ input, reason, expected } = pure (input, cutfailWith reason expected)
{-# INLINE cutfailk #-}


-- | Fail to parse, providing the given document as a reason.
--
-- @
-- 'emptyWith' 'Nothing' 'mempty' = 'empty'
-- @
emptyWith :: Maybe String -> Set String -> ParserC m a
emptyWith   a e = ParserC (\ _ nil _    i -> nil  (Err i a e))
{-# INLINE emptyWith #-}

-- | Fail to parse and prevent backtracking, providing the given document as a reason.
--
-- @
-- 'cutfailWith' 'Nothing' 'mempty' = 'cutfail'
-- @
cutfailWith :: Maybe String -> Set String -> ParserC m a
cutfailWith a e = ParserC (\ _ _   fail i -> fail (Err i a e))
{-# INLINE cutfailWith #-}


-- FIXME: Text
-- FIXME: rope of Text
-- FIXME: a lazy stream/iteratee/whatever of ropes of Text
data Input = Input
  { pos :: {-# UNPACK #-} !Pos
  , str :: !String
  }
  deriving (Eq, Ord, Show)

pos_ :: Lens' Input Pos
pos_ = lens pos $ \ i pos -> i{ pos }
{-# INLINE pos_ #-}

str_ :: Lens' Input String
str_ = lens str $ \ i str -> i{ str }
{-# INLINE str_ #-}

advance :: Input -> Input
advance = \case
  Input pos (c:cs) -> Input (advancePos c pos) cs
  i                -> i
{-# INLINE advance #-}

advancePos :: Char -> Pos -> Pos
advancePos c p = case c of
  -- FIXME: this should handle CR & maybe CRLF
  '\n' -> Pos (succ (Span.line p)) 0
  _    -> p { Span.column = succ (Span.column p) }
{-# INLINE advancePos #-}


data Err = Err
  { input    :: {-# UNPACK #-} !Input
  , reason   :: !(Maybe String)
  , expected :: !(Set String)
  }
  deriving (Eq, Ord, Show)

input_ :: Lens' Err Input
input_ = lens input $ \ i input -> i{ input }
{-# INLINE input_ #-}

reason_ :: Lens' Err (Maybe String)
reason_ = lens reason $ \ i reason -> i{ reason }
{-# INLINE reason_ #-}

expected_ :: Lens' Err (Set String)
expected_ = lens expected $ \ i expected -> i{ expected }
{-# INLINE expected_ #-}
