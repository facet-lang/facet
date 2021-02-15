{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Facet.Snoc
( Snoc(..)
, fromList
, pattern FromList
, (!)
, (!?)
, peek
) where

import Data.Foldable (foldl', foldr')
import Data.Functor.Classes
import Data.Semialign
import Data.These
import Facet.Semiring
import GHC.Exts
import GHC.Stack

data Snoc a
  = Nil
  | Snoc a :> a
  deriving (Eq, Foldable, Functor, Ord, Traversable)

infixl 5 :>

instance Show a => Show (Snoc a) where
  showsPrec _ s = showString "fromList" . showChar ' ' . showList (toList s)

instance Semigroup (Snoc a) where
  a <> Nil       = a
  a <> (bs :> b) = (a <> bs) :> b

instance Monoid (Snoc a) where
  mempty = Nil

instance Semiring r => LeftModule r (Snoc r) where
  (><<) = scaleDefault

instance Semialign Snoc where
  align Nil     Nil     = Nil
  align Nil     bs      = That <$> bs
  align as      Nil     = This <$> as
  align (as:>a) (bs:>b) = align as bs :> These a b

instance Zip Snoc where
  zipWith f = go
    where
    go = curry $ \case
      (as:>a, bs:>b) -> go as bs :> f a b
      _              -> Nil

instance Applicative Snoc where
  pure = (Nil :>)
  fs <*> as = go id fs as
    where
    go accum Nil     _  = accum Nil
    go accum (fs:>f) as = go (accum . flip (foldl (\ fas a -> fas :> f a)) as) fs as

instance Monad Snoc where
  as >>= f = go id as
    where
    go accum Nil     = accum Nil
    go accum (as:>a) = go (accum . (<> f a)) as

instance Eq1 Snoc where
  liftEq eq = go
    where
    go Nil      Nil      = True
    go (s1:>a1) (s2:>a2) = eq a1 a2 && go s1 s2
    go _        _        = False

instance Ord1 Snoc where
  liftCompare compare = go
    where
    go Nil      Nil      = EQ
    go (s1:>a1) (s2:>a2) = compare a1 a2 <> go s1 s2
    go Nil      _        = LT
    go _        _        = GT


pattern FromList :: [a] -> Snoc a
pattern FromList xs <- (toList -> xs)
  where
  FromList xs = fromList xs


instance IsList (Snoc a) where
  type Item (Snoc a) = a

  toList   = foldr' (:)  []
  fromList = foldl' (:>) Nil


-- | Unsafe indexing (throws an exception for out-of-bounds indices).
--
-- The index functions like a De Bruijn index, counting down from the /top/ of the stack (i.e. right-to-left).
(!) :: HasCallStack => Snoc a -> Int -> a
as' ! i' = withFrozenCallStack $ go as' i'
  where
  go (as :> a) i
    | i == 0     = a
    | otherwise  = go as (i - 1)
  go _         _ = error $ "Facet.Snoc.!: index (" <> show i' <> ") out of bounds (" <> show (length as') <> ")"

-- | Safe indexing.
--
-- The index functions like a De Bruijn index, counting down from the /top/ of the stack (i.e. right-to-left).
(!?) :: Snoc a -> Int -> Maybe a
Nil       !? _ = Nothing
(_  :> a) !? 0 = Just a
(as :> _) !? i = as !? (i - 1)

-- | Safe retrieval of the top of the stack.
peek :: Snoc a -> Maybe a
peek = \case
  _ :> h -> Just h
  _      -> Nothing
