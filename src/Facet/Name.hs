module Facet.Name
( Index(..)
, Level(..)
, levelToIndex
, indexToLevel
, Meta(..)
, __
, MName
, prettyMName
, Q(..)
, Name(..)
, Assoc(..)
, Op(..)
, OpN(..)
) where

import           Data.Foldable (foldr')
import           Data.Functor.Classes (showsUnaryWith)
import qualified Data.List.NonEmpty as NE
import           Data.String (IsString(..))
import           Data.Text (Text)
import qualified Data.Text as T
import           Facet.Stack
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

levelToIndex :: Level -> Level -> Index
levelToIndex (Level d) (Level level) = Index $ d - level - 1

indexToLevel :: Level -> Index -> Level
indexToLevel (Level d) (Index index) = Level $ d - index - 1


newtype Meta = Meta { getMeta :: Int }
  deriving (Eq, Ord, Show)


__ :: Name
__ = U T.empty


type MName = Stack Text

prettyMName :: Printer a => MName -> a
prettyMName = \case
  Nil   -> mempty
  ns:>n -> foldr' (surround dot . pretty) (pretty n) ns


-- | Qualified names, consisting of a module name and declaration name.
data Q a = MName :.: a -- FIXME: use Name on the lhs so we can accommodate datatypes with operator names
  deriving (Eq, Ord, Show)

instance P.Pretty a => P.Pretty (Q a) where
  pretty (m :.: n) = foldr' (surround dot . pretty) (pretty n) m


-- | Declaration names; a choice of expression, constructor, term, or operator names.
data Name
  = U Text
  | O Op
  deriving (Eq, Ord, Show)

instance IsString Name where
  fromString = U . fromString

instance P.Pretty Name where
  pretty = \case
    U n -> P.pretty n
    O o -> P.pretty o


-- | Associativity of an infix operator.
data Assoc = N | L | R | A
  deriving (Eq, Ord, Show)

-- | Mixfix operator names, restricted to unary (prefix, postfix, outfix) & binary (infix).
data Op
  = Prefix  Text
  | Postfix Text
  | Infix   Text
  | Outfix Text Text
  deriving (Eq, Ord, Show)

-- FIXME: specify relative precedences

instance P.Pretty Op where
  pretty = \case
    Prefix   s -> P.pretty s <+> place
    Postfix  s -> place <+> P.pretty s
    Infix    s -> place <+> P.pretty s <+> place
    Outfix s e -> P.pretty s <+> place <+> P.pretty e
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
