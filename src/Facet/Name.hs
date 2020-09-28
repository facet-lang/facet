{-# LANGUAGE TupleSections #-}
module Facet.Name
( Name(..)
, prime
, prettyName
, __
, Scoped(..)
, binder
, binderM
) where

import           Control.Monad.Fix
import           Data.Function (on)
import qualified Data.Text as T
import           Facet.Pretty
import qualified Prettyprinter as P
import           Silkscreen

data Name = Name { name :: T.Text, id' :: Int }

instance Eq Name where
  (==) = (==) `on` id'

instance Ord Name where
  compare = compare `on` id'

instance Show Name where
  showsPrec p = showsPrec p . P.pretty

instance P.Pretty Name where
  pretty = prettyName

prettyName :: Printer p => Name -> p
prettyName n
  | T.null (name n) = var (id' n)
  | otherwise       = pretty (name n) <> pretty (id' n)
  where
  var = varFrom ['a'..'z']
  varFrom alpha i = pretty (toAlpha alpha i)


prime :: T.Text -> Maybe Int -> Name
prime n i = Name n (maybe 0 succ i)


__ :: T.Text
__ = T.empty


class Scoped t where
  maxBV :: t -> Maybe Int

instance Scoped Name where
  maxBV = Just . id'

binder
  :: Scoped t
  => (Name -> t)
  -> (Name -> t -> r)
  -> T.Text
  -> (t -> t)
  -> r
binder bound ctor n e = ctor n' b'
  where
  b' = e (bound n')
  n' = prime n (maxBV b')

binderM
  :: (Scoped t, MonadFix m)
  => (Name -> t)
  -> (Name -> t -> r)
  -> T.Text
  -> (t -> m t)
  -> m r
binderM bound ctor n e = uncurry ctor <$> mfix (\ ~(n', b') -> do
  (prime n (maxBV b'),) <$> e (bound n'))
