-- | Really just a snoc list, but the shoe fits if you squish things up just right.
module Facet.Stack
( Stack(..)
, fromList
, (!)
, (!?)
) where

import Data.Foldable (foldl', toList)
import Data.Functor.Classes
import Data.Semialign
import Data.These
import GHC.Stack

data Stack a
  = Nil
  | Stack a :> a
  deriving (Eq, Foldable, Functor, Ord, Traversable)

infixl 5 :>

instance Show a => Show (Stack a) where
  showsPrec _ s = showString "fromList" . showChar ' ' . showList (toList s)

instance Semigroup (Stack a) where
  a <> Nil       = a
  a <> (bs :> b) = (a <> bs) :> b

instance Monoid (Stack a) where
  mempty = Nil

instance Semialign Stack where
  align Nil     Nil     = Nil
  align Nil     bs      = That <$> bs
  align as      Nil     = This <$> as
  align (as:>a) (bs:>b) = align as bs :> These a b

instance Zip Stack where
  zipWith f = go
    where
    go = curry $ \case
      (as:>a, bs:>b) -> go as bs :> f a b
      _              -> Nil

instance Applicative Stack where
  pure = (Nil :>)
  fs <*> as = go id fs as
    where
    go accum Nil     _  = accum Nil
    go accum (fs:>f) as = go (accum . flip (foldl (\ fas a -> fas :> f a)) as) fs as

instance Monad Stack where
  as >>= f = go id as
    where
    go accum Nil     = accum Nil
    go accum (as:>a) = go (accum . (<> f a)) as

instance Eq1 Stack where
  liftEq eq = go
    where go Nil      Nil      = True
          go (s1:>a1) (s2:>a2) = eq a1 a2 && go s1 s2
          go _        _        = False

instance Ord1 Stack where
  liftCompare compare = go
    where go Nil      Nil      = EQ
          go (s1:>a1) (s2:>a2) = compare a1 a2 <> go s1 s2
          go Nil      _        = LT
          go _        _        = GT


fromList :: [a] -> Stack a
fromList = foldl' (:>) Nil


-- | Unsafe indexing (throws an exception for out-of-bounds indices).
--
-- The index functions like a De Bruijn index, counting down from the /top/ of the stack (i.e. right-to-left).
(!) :: HasCallStack => Stack a -> Int -> a
as' ! i' = withFrozenCallStack $ go as' i'
  where
  go (as :> a) i
    | i == 0     = a
    | otherwise  = go as (i - 1)
  go _         _ = error $ "Facet.Stack.!: index (" <> show i' <> ") out of bounds (" <> show (length as') <> ")"

-- | Safe indexing (returns 'Nothing' for out-of-bounds indices).
--
-- The index functions like a De Bruijn index, counting down from the /top/ of the stack (i.e. right-to-left).
(!?) :: Stack a -> Int -> Maybe a
(as :> a) !? i
  | i == 0     = Just a
  | otherwise  = as !? (i - 1)
_         !? _ = Nothing
