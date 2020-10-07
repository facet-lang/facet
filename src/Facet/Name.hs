{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Name
( Name(..)
, prettyNameWith
, eqN
, elemN
, E
, T
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

import           Data.Coerce
import           Data.Function (on)
import qualified Data.IntMap as IntMap
import           Data.List.NonEmpty
import           Data.String (IsString(..))
import           Data.Text (Text, unpack)
import qualified Data.Text as T
import           Facet.Pretty
import qualified Prettyprinter as P
import           Silkscreen

data Name a = Name { hint :: Text, id' :: Int }

instance Eq (Name a) where
  (==) = (==) `on` id'

instance Ord (Name a) where
  compare = compare `on` id'

instance Show (Name a) where
  showsPrec _ (Name h i) = showString (unpack h) . shows i

instance P.Pretty (Name E) where
  pretty = prettyNameWith evar

instance P.Pretty (Name T) where
  pretty = prettyNameWith tvar


prettyNameWith :: Printer p => (Int -> p) -> Name a -> p
prettyNameWith var n
  | T.null (hint n) = var (id' n)
  | otherwise       = pretty (hint n) <> pretty (id' n)

eqN :: Name a -> Name b -> Bool
eqN = coerce ((==) :: Name a -> Name a -> Bool)

elemN :: Foldable t => Name b -> t (Name a) -> Bool
elemN = elem . coerce


data E
data T


__ :: Text
__ = T.empty


instantiate :: Name a -> t -> IntMap.IntMap t -> IntMap.IntMap t
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
