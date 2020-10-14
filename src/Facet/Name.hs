{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Name
( UName(..)
, Index(..)
, Level(..)
, levelToIndex
, indexToLevel
, incrLevel
, incrLevelFor
, shiftLevel
, isMeta
, WithAnn(..)
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

import           Data.Functor.Classes (showsUnaryWith)
import           Data.List.NonEmpty
import           Data.String (IsString(..))
import           Data.Text (Text, unpack)
import qualified Data.Text as T
import           Data.Traversable (mapAccumR)
import qualified Prettyprinter as P
import           Silkscreen

-- | User-supplied name.
newtype UName = UName { getUName :: Text }
  deriving (Eq, IsString, Ord)

instance Show UName where
  showsPrec _ = showString . unpack . getUName

instance P.Pretty UName where
  pretty = P.pretty . getUName


-- | De Bruijn indices, counting up from the binding site to the reference site (“inside out”).
newtype Index = Index { getIndex :: Int }
  deriving (Eq, Ord)

instance Show Index where
  showsPrec p = showsUnaryWith showsPrec "Index" p . getIndex

-- | De Bruijn indices, counting up from the root to the binding site (“outside in”).
newtype Level = Level { getLevel :: Int }
  deriving (Eq, Ord)

instance Show Level where
  showsPrec p = showsUnaryWith showsPrec "Level" p . getLevel

levelToIndex :: Level -> Level -> Index
levelToIndex (Level d) (Level level) = Index $ d - level - 1

indexToLevel :: Int -> Index -> Level
indexToLevel d (Index index) = Level $ d - index - 1

incrLevel :: Level -> Level
incrLevel (Level l) = Level (l + 1)

incrLevelFor :: Traversable t => (Level -> expr) -> Level -> t UName -> (Level, t expr)
incrLevelFor mk = mapAccumR $ \ l _ -> (incrLevel l, mk l)

shiftLevel :: Level -> Level -> Level
shiftLevel (Level l) (Level r) = Level (l + r)

isMeta :: Level -> Bool
isMeta (Level l) = l < 0


data WithAnn a b = WithAnn
  { ann :: a
  , val :: b
  }
  deriving (Foldable, Functor, Traversable)


__ :: UName
__ = UName T.empty


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
newtype EName = EName { getEName :: UName }
  deriving newtype (Eq, IsString, Ord, P.Pretty, Show)

-- | Constructor names, as provided by the user.
newtype CName = CName { getCName :: UName }
  deriving newtype (Eq, IsString, Ord, P.Pretty, Show)

-- | Type names, as provided by the user.
newtype TName = TName { getTName :: UName }
  deriving newtype (Eq, IsString, Ord, P.Pretty, Show)

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
