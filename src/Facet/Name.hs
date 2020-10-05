{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
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
, DName(..)
, Assoc(..)
, Op(..)
) where

import           Data.Function (on)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import           Data.List.NonEmpty
import           Data.String (IsString(..))
import           Data.Text (Text)
import qualified Data.Text as T
import           Facet.Pretty
import qualified Prettyprinter as P
import           Silkscreen

data Name = Name { hint :: Text, id' :: Int }

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


prime :: Scoped t => Text -> t -> Name
prime n t
  | IntSet.null fvs' = Name n 0
  | otherwise        = Name n (IntSet.findMax fvs' + 1)
  where
  fvs' = fvs t


__ :: Text
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
  = MName Text
  | MName :. Text
  deriving (Eq, Ord, Show)

data QName = MName :.: DName
  deriving (Eq, Ord, Show)

moduleName :: QName -> MName
moduleName (mname :.: _) = mname


newtype EName = EName { getEName :: Text }
  deriving (Eq, IsString, Ord, P.Pretty, Show)

newtype TName = TName { getTName :: Text }
  deriving (Eq, IsString, Ord, P.Pretty, Show)

data DName
  = E EName
  | T TName
  deriving (Eq, Ord, Show)

instance P.Pretty DName where
  pretty = \case
    E n -> P.pretty n
    T n -> P.pretty n


data Assoc = N | L | R
  deriving (Eq, Ord, Show)

data Op
  = Prefix      Text   [Text]
  | Postfix     [Text] Text
  | Infix Assoc (NonEmpty Text)
  | Outfix Text [Text] Text
  deriving (Eq, Ord, Show)
