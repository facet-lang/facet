{-# LANGUAGE TupleSections #-}
module Facet.Name
( Name(..)
, prime
, prettyNameWith
, __
, Scoped(..)
, binder
, binderM
, instantiate
) where

import           Control.Monad.Fix
import           Data.Function (on)
import qualified Data.IntMap as IntMap
import           Data.Semigroup (Max(..))
import qualified Data.Text as T
import           Facet.Pretty
import qualified Prettyprinter as P
import           Silkscreen

data Name = Name { hint :: T.Text, id' :: Int }

instance Eq Name where
  (==) = (==) `on` id'

instance Ord Name where
  compare = compare `on` id'

instance Show Name where
  showsPrec p = showsPrec p . P.pretty

instance P.Pretty Name where
  pretty = prettyNameWith var

prettyNameWith :: Printer p => (Int -> p) -> Name -> p
prettyNameWith var n
  | T.null (hint n) = var (id' n)
  | otherwise       = pretty (hint n) <> pretty (id' n)


prime :: T.Text -> Maybe (Max Int) -> Name
prime n i = Name n (maybe 0 (succ . getMax) i)


__ :: T.Text
__ = T.empty


class Scoped t where
  maxBV :: t -> Maybe (Max Int)

instance Scoped Name where
  maxBV = Just . Max . id'

binder
  :: Scoped t
  => (Name -> d)
  -> (Name -> t -> r)
  -> T.Text
  -> (d -> t)
  -> r
binder bound ctor n e = ctor n' b'
  where
  b' = e (bound n')
  n' = prime n (maxBV b')

binderM
  :: (Scoped t, MonadFix m)
  => (Name -> d)
  -> (Name -> t -> r)
  -> T.Text
  -> (d -> m t)
  -> m r
binderM bound ctor n e = uncurry ctor <$> mfix (\ ~(n', b') -> do
  (prime n (maxBV b'),) <$> e (bound n'))


instantiate :: Name -> t -> IntMap.IntMap t -> IntMap.IntMap t
instantiate = IntMap.insert . id'
