{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Syntax.Common
( (:::)(..)
, (.:)
, ForAll(..)
, hoistForAll
) where

data a ::: b = a ::: b
  deriving (Eq, Ord, Show)

infix 5 :::


(.:) :: Functor m => m a -> b -> m (a ::: b)
tm .: ty = (::: ty) <$> tm

infix 5 .:


newtype ForAll f = Abstract { instantiate :: forall x . f x }

hoistForAll :: (forall x . f x -> g x) -> ForAll f -> ForAll g
hoistForAll f t = Abstract (f (instantiate t))
