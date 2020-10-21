module Facet.Name
( UName(..)
, Index(..)
, Level(..)
, levelToIndex
, indexToLevel
, Meta(..)
, FVs(..)
, getFVs
, Vars(..)
, Silent(..)
, __
, MName(..)
, QName(..)
, moduleName
, CName(..)
, DName(..)
, Assoc(..)
, Op(..)
, OpN(..)
) where

import           Data.Function (on)
import           Data.Functor.Classes (showsUnaryWith)
import qualified Data.IntSet as IntSet
import           Data.List.NonEmpty hiding (cons)
import           Data.Semigroup
import           Data.String (IsString(..))
import           Data.Text (Text, unpack)
import qualified Data.Text as T
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
  deriving (Enum, Eq, Ord)

instance Show Level where
  showsPrec p = showsUnaryWith showsPrec "Level" p . getLevel

levelToIndex :: Level -> Level -> Index
levelToIndex (Level d) (Level level) = Index $ d - level - 1

indexToLevel :: Level -> Index -> Level
indexToLevel (Level d) (Index index) = Level $ d - index - 1


newtype Meta = Meta { getMeta :: Int }
  deriving (Eq, Ord, Show)


newtype FVs = FVs { runFVs :: IntSet.IntSet -> IntSet.IntSet -> IntSet.IntSet }

getFVs :: FVs -> IntSet.IntSet
getFVs v = runFVs v mempty mempty

instance Semigroup FVs where
  FVs v1 <> FVs v2 = FVs $ \ b -> v1 b . v2 b

  stimes = stimesIdempotentMonoid

instance Monoid FVs where
  mempty = FVs $ const id


class Monoid v => Vars v where
  use :: Level -> v
  use l = cons l mempty
  cons :: Level -> v -> v
  cons l v = use l <> v
  bind :: Level -> v -> v

  {-# MINIMAL (use|cons), bind #-}

instance Vars FVs where
  use (Level l) = FVs $ \ b -> if l `IntSet.member` b then id else IntSet.insert l
  cons (Level l) (FVs v) = FVs $ \ b -> v b . if l `IntSet.member` b then id else IntSet.insert l
  bind (Level l) (FVs r) = FVs $ \ b -> r (IntSet.insert l b)

instance Vars b => Vars (a -> b) where
  use l = pure (use l)
  cons l = fmap (cons l)
  bind l = fmap (cons l)

instance (Vars a, Vars b) => Vars (a, b) where
  use l = (use l, use l)
  cons l (a, b) = (cons l a, cons l b)
  bind l (a, b) = (bind l a, bind l b)


data Silent a b = Silent
  { ann :: a
  , val :: b
  }
  deriving (Foldable, Functor, Traversable)

instance Eq b => Eq (Silent a b) where
  (==) = (==) `on` val

instance Ord b => Ord (Silent a b) where
  compare = compare `on` val

instance Show b => Show (Silent a b) where
  showsPrec p = showsPrec p . val


__ :: UName
__ = UName T.empty


-- | Module names.
data MName
  = MName Text
  | MName :. Text
  deriving (Eq, Ord, Show)

instance P.Pretty MName where
  pretty (n :. s)  = pretty n <> dot <> pretty s
  pretty (MName s) = pretty s


-- | Qualified names, consisting of a module name and declaration name.
data QName = MName :.: DName
  deriving (Eq, Ord, Show)

instance P.Pretty QName where
  pretty (m :.: n) = pretty m <> dot <> pretty n

moduleName :: QName -> MName
moduleName (mname :.: _) = mname


-- | Constructor names, as provided by the user.
newtype CName = CName { getCName :: UName }
  deriving newtype (Eq, IsString, Ord, P.Pretty, Show)

-- | Declaration names; a choice of expression, term, or operator names.
data DName
  = E UName
  | C UName
  | T UName
  | O Op
  deriving (Eq, Ord, Show)

instance P.Pretty DName where
  pretty = \case
    E n -> P.pretty n
    C n -> P.pretty n
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
