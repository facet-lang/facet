{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Name
( Name(..)
, name
, prettyNameWith
, eqN
, elemN
, UName(..)
, E
, T
, __
, MName(..)
, QName(..)
, moduleName
, EName(..)
, CName(..)
, TName(..)
, DName(..)
, Assoc(..)
, Op(..)
, OpN(..)
) where

import           Data.Coerce
import           Data.Function (on)
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


name :: Text -> Int -> Name a
name = Name

prettyNameWith :: Printer p => (Int -> p) -> Name a -> p
prettyNameWith var n
  | T.null (hint n) = var (id' n)
  | otherwise       = pretty (hint n) <> pretty (id' n)

eqN :: Name a -> Name b -> Bool
eqN = coerce ((==) :: Name a -> Name a -> Bool)

elemN :: Foldable t => Name b -> t (Name a) -> Bool
elemN = elem . coerce


-- | User-supplied name.
--
-- These always compare as equal, and so are useful for /preserving/ variable names for e.g. error messages without compromising alpha-equivalence.
newtype UName = UName { getUName :: Text }

instance Eq UName where
  _ == _ = True

instance Ord UName where
  compare _ _ = EQ

instance Show UName where
  showsPrec _ = showString . unpack . getUName

instance P.Pretty UName where
  pretty = P.pretty . getUName


data E
data T


__ :: Text
__ = T.empty


-- | Module names.
data MName
  = MName Text
  | MName :. Text
  deriving (Eq, Ord, Show)

-- | Qualified names, consisting of a module name and declaration name.
data QName = MName :.: DName
  deriving (Eq, Ord, Show)

moduleName :: QName -> MName
moduleName (mname :.: _) = mname


-- | Expression names, as provided by the user.
newtype EName = EName { getEName :: Text }
  deriving (Eq, IsString, Ord, P.Pretty, Show)

-- | Constructor names, as provided by the user.
newtype CName = CName { getCName :: Text }
  deriving (Eq, IsString, Ord, P.Pretty, Show)

-- | Type names, as provided by the user.
newtype TName = TName { getTName :: Text }
  deriving (Eq, IsString, Ord, P.Pretty, Show)

-- | Declaration names; a choice of expression, term, or operator names.
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


-- | Associativity of an infix operator.
data Assoc = N | L | R
  deriving (Eq, Ord, Show)

-- | Mixfix operators, restricted to unary (prefix, postfix, outfix) & binary (infix).
data Op
  = Prefix  Text
  | Postfix Text
  | Infix Assoc Text
  | Outfix Text Text
  deriving (Eq, Ord, Show)

-- FIXME: specify relative precedences

instance P.Pretty Op where
  pretty = \case
    Prefix   s -> P.pretty s <+> place
    Postfix  s -> place <+> P.pretty s
    Infix  _ s -> place <+> P.pretty s <+> place
    Outfix s e -> P.pretty s <+> place <+> P.pretty e
    where
    place = P.pretty '_'


-- | Mixfix operators, supporting a broader set of names.
--
-- Not currently used because parsing will require type indices to ensure that the constructors line up with the number of places, i.e. vectors and such.
data OpN
  = PrefixN      Text   [Text]
  | PostfixN     [Text] Text
  | InfixN Assoc (NonEmpty Text)
  | OutfixN Text [Text] Text
  deriving (Eq, Ord, Show)

-- FIXME: can we treat this more compositionally instead? i.e. treat an n-ary prefix operator as a composition of individual prefix operators? Then each placeholder lines up with a unary operator corresponding to the type of the tail
