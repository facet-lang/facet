{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
module Facet.Snoc.NonEmpty
( NonEmpty(..)
, (|>)
, fromSnoc
, nonEmpty
, toSnoc
, pattern FromList
) where

import Data.Foldable (foldr')
import Facet.Snoc hiding (FromList)
import GHC.Exts

data NonEmpty a = Snoc a :|> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 5 :|>

(|>) :: NonEmpty a -> a -> NonEmpty a
i :|> l |> l' = i :> l :|> l'

infixl 5 |>


fromSnoc :: Snoc a -> NonEmpty a
fromSnoc = \case
  Nil   -> error "fromSnoc: empty snoc"
  as:>a -> as:|>a

nonEmpty :: Snoc a -> Maybe (NonEmpty a)
nonEmpty = \case
  Nil   -> Nothing
  as:>a -> Just (as:|>a)

toSnoc :: NonEmpty a -> Snoc a
toSnoc (as:|>a) = as:>a


pattern FromList :: [a] -> NonEmpty a
pattern FromList xs <- (toList -> xs)
  where
  FromList xs = fromList xs


instance IsList (NonEmpty a) where
  type Item (NonEmpty a) = a

  toList          = foldr' (:)  []
  fromList (x:xs) = foldl' (|>) (Nil :|> x) xs
  fromList []     = error "fromList: empty list"
