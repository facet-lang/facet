{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Syntax.Common
( (:::)(..)
, (.:)
, ForAll(..)
, hoistForAll
, sequenceForAllMaybe
, ForAll1(..)
, hoistForAll1
) where

import Data.Maybe (fromJust)
import Facet.Functor.C

data a ::: b = a ::: b
  deriving (Eq, Ord, Show)

infix 5 :::


(.:) :: Functor m => m a -> b -> m (a ::: b)
tm .: ty = (::: ty) <$> tm

infix 5 .:


newtype ForAll f = Abstract { instantiate :: forall x . f x }

hoistForAll :: (forall x . f x -> g x) -> ForAll f -> ForAll g
hoistForAll f t = Abstract (f (instantiate t))

sequenceForAllMaybe :: ForAll (Maybe :.: f) -> Maybe (ForAll f)
sequenceForAllMaybe t = case instantiate t of
  C Nothing  -> Nothing
  C (Just _) -> Just (hoistForAll (fromJust . getC) t)


newtype ForAll1 f a = Abstract1 { instantiate1 :: forall x . f x a }

hoistForAll1 :: (forall x . f x a -> g x a) -> ForAll1 f a -> ForAll1 g a
hoistForAll1 f t = Abstract1 (f (instantiate1 t))
