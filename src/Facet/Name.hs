{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
module Facet.Name
( Name(..)
, prettyNameWith
, prime
, __
, FVs
, Scoped(..)
, instantiate
, MName(..)
, QName(..)
, moduleName
, EName(..)
, TName(..)
) where

import           Data.Function (on)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import           Data.String (IsString(..))
import           Data.Text (Text)
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


prime :: Scoped t => T.Text -> t -> Name
prime n t
  | IntSet.null fvs' = Name n 0
  | otherwise        = Name n (IntSet.findMax fvs' + 1)
  where
  fvs' = fvs t


__ :: T.Text
__ = T.empty


type FVs = IntSet.IntSet

class Scoped t where
  fvs :: t -> FVs

instance Scoped IntSet.IntSet where
  fvs = id

instance Scoped Name where
  fvs = IntSet.singleton . id'


instantiate :: Name -> t -> IntMap.IntMap t -> IntMap.IntMap t
instantiate = IntMap.insert . id'


data MName
  = MName T.Text
  | MName :. T.Text
  deriving (Eq, Ord, Show)

data QName = MName :.: T.Text
  deriving (Eq, Ord, Show)

moduleName :: QName -> MName
moduleName (mname :.: _) = mname


newtype EName = EName { getEName :: Text }
  deriving (Eq, IsString, Ord, P.Pretty, Show)

newtype TName = TName { getTName :: Text }
  deriving (Eq, IsString, Ord, P.Pretty, Show)
