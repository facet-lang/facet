{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Name
( Name(..)
, prettyNameWith
, __
, instantiate
, MName(..)
, QName(..)
, moduleName
, EName(..)
, TName(..)
, DName(..)
, Assoc(..)
, Op(..)
, OpN(..)
) where

import           Data.Function (on)
import qualified Data.IntMap as IntMap
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
  pretty = prettyNameWith evar

prettyNameWith :: Printer p => (Int -> p) -> Name -> p
prettyNameWith var n
  | T.null (hint n) = var (id' n)
  | otherwise       = pretty (hint n) <> pretty (id' n)


__ :: Text
__ = T.empty


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
  | O Op
  deriving (Eq, Ord, Show)

instance P.Pretty DName where
  pretty = \case
    E n -> P.pretty n
    T n -> P.pretty n
    O o -> P.pretty o


data Assoc = N | L | R
  deriving (Eq, Ord, Show)

data Op
  = Prefix  Text
  | Postfix Text
  | Infix Assoc Text
  | Outfix Text Text
  deriving (Eq, Ord, Show)

instance P.Pretty Op where
  pretty = \case
    Prefix   s -> P.pretty s <+> place
    Postfix  s -> place <+> P.pretty s
    Infix  _ s -> place <+> P.pretty s <+> place
    Outfix s e -> P.pretty s <+> place <+> P.pretty e
    where
    place = P.pretty '_'

data OpN
  = PrefixN      Text   [Text]
  | PostfixN     [Text] Text
  | InfixN Assoc (NonEmpty Text)
  | OutfixN Text [Text] Text
  deriving (Eq, Ord, Show)
