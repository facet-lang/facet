{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Name
( Index(..)
, Level(..)
, DeBruijn(..)
, Meta(..)
, __
, QName(..)
, (//)
, q
, qlast
, qlocal
, fromSnoc
, toSnoc
, Name(..)
, Assoc(..)
, Op(..)
, formatOp
, OpN(..)
, formatOpN
) where

import           Data.Foldable (foldl', foldr')
import           Data.Functor.Classes (showsUnaryWith)
import           Data.List (intercalate)
import qualified Data.List.NonEmpty as NE
import           Data.Text (Text, pack, unpack)
import qualified Data.Text as T
import           Facet.Pretty (subscript, subscriptWith)
import           Facet.Snoc
import qualified Facet.Snoc.NonEmpty as SNE
import           GHC.Exts
import qualified Prettyprinter as P
import           Silkscreen

-- | De Bruijn indices, counting up from the binding site to the reference site (“inside out”).
newtype Index = Index { getIndex :: Int }
  deriving (Enum, Eq, Num, Ord)

instance Show Index where
  showsPrec p = showsUnaryWith showsPrec "Index" p . getIndex

-- | De Bruijn indices, counting up from the root to the binding site (“outside in”).
newtype Level = Level { getLevel :: Int }
  deriving (Enum, Eq, Num, Ord)

instance Show Level where
  showsPrec p = showsUnaryWith showsPrec "Level" p . getLevel


class DeBruijn lv ix | lv -> ix, ix -> lv where
  toIndexed :: Level -> lv -> ix
  toLeveled :: Level -> ix -> lv

instance DeBruijn Level Index where
  toIndexed (Level d) (Level level) = Index $ d - level - 1
  toLeveled (Level d) (Index index) = Level $ d - index - 1

instance DeBruijn lv ix => DeBruijn (Either e lv) (Either e ix) where
  toIndexed = fmap . toIndexed
  toLeveled = fmap . toLeveled


newtype Used = Used { getUsed :: Level }
  deriving (Enum, Eq, Num, Ord)

instance Show Used where
  showsPrec p = showsUnaryWith showsPrec "Used" p . getUsed


newtype Meta = Meta { getMeta :: Int }
  deriving (Eq, Ord, Show)


__ :: Name
__ = T T.empty


-- | Qualified names, consisting of a module name and declaration name.
newtype QName = QName { getQName :: SNE.NonEmpty Name }
  deriving (Eq, Ord)

instance IsList QName where
  type Item QName = Name
  fromList = QName . fromList
  toList = toList . getQName

instance IsString QName where
  fromString = QName . SNE.fromSnoc . go Nil
    where
    go accum s = let (name, rest) = span (/= '.') s in case rest of
      '.':s' -> go (accum :> T (pack name)) s'
      _      -> accum :> T (pack name)

instance Pretty QName where
  pretty (QName (ns SNE.:|> n)) = foldr' (surround dot . pretty) (pretty n) ns

instance Show QName where
  showsPrec _ (QName components) = showString (intercalate "." (map show (toList components)))

(//) :: QName -> Name -> QName
q // n = QName (getQName q SNE.|> n)

infixl 5 //

q :: Name -> QName
q = QName . (Nil SNE.:|>)

qlast :: QName -> Name
qlast (QName (_ SNE.:|> l)) = l

qlocal :: QName -> Maybe Name
qlocal (QName (Nil SNE.:|> n)) = Just n
qlocal _                       = Nothing

fromSnoc :: Snoc Name -> QName
fromSnoc = QName . SNE.fromSnoc

toSnoc :: QName -> Snoc Name
toSnoc = SNE.toSnoc . getQName


-- | Declaration names; a choice of textual or operator names.
data Name
  = T Text
  | O Op
  | G Text Int
  deriving (Eq, Ord)

instance IsString Name where
  fromString = T . fromString

instance P.Pretty Name where
  pretty = \case
    T n   -> P.pretty n
    O o   -> P.pretty o
    G n i -> P.pretty n <> subscript i

instance Show Name where
  showsPrec p = \case
    T n   -> showString (unpack n)
    O o   -> showsPrec p o
    G n i -> showString (unpack n) . subscriptWith (.) showChar id i


-- | Associativity of an infix operator.
data Assoc = N | L | R | A
  deriving (Eq, Ord, Show)

-- | Mixfix operator names, restricted to unary (prefix, postfix, outfix) & binary (infix).
data Op
  = Prefix  Text
  | Postfix Text
  | Infix   Text
  | Outfix Text Text
  deriving (Eq, Ord)

instance Show Op where
  showsPrec _ = formatOp (\ a b -> a . showChar ' ' . b) (showString . unpack) (showChar '_')

formatOp :: (a -> a -> a) -> (Text -> a) -> a -> Op -> a
formatOp (<+>) pretty place = \case
  Prefix   s -> pretty s <+> place
  Postfix  s -> place <+> pretty s
  Infix    s -> place <+> pretty s <+> place
  Outfix s e -> pretty s <+> place <+> pretty e

-- FIXME: specify relative precedences

instance P.Pretty Op where
  pretty = formatOp (<+>) P.pretty place
    where
    place = P.pretty '_'


-- | Mixfix operator names, supporting a broader set of names.
--
-- Not currently used because parsing will require type indices to ensure that the constructors line up with the number of places, i.e. vectors and such.
data OpN
  = PrefixN  Text   [Text]
  | PostfixN [Text] Text
  | InfixN   (NE.NonEmpty Text)
  | OutfixN Text [Text] Text
  deriving (Eq, Ord, Show)

-- FIXME: can we treat this more compositionally instead? i.e. treat an n-ary prefix operator as a composition of individual prefix operators? Then each placeholder lines up with a unary operator corresponding to the type of the tail

formatOpN :: (a -> a -> a) -> (Text -> a) -> a -> OpN -> a
formatOpN (<+>) pretty place = \case
  PrefixN   s ss        -> foldl' (<+>) (comp s) (map comp ss) where comp s = pretty s <+> place
  PostfixN  ee e        -> foldr' (<+>) (comp e) (map comp ee) where comp e = place <+> pretty e
  InfixN    (m NE.:|mm) -> place <+> foldr' comp (pretty m) mm <+> place where comp s e = pretty s <+> place <+> e
  OutfixN s mm e        -> foldr' comp (pretty e) (s : mm) where comp s e = pretty s <+> place <+> e
