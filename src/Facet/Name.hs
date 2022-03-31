{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Name
( Index(..)
, Level(..)
, DeBruijn(..)
, Used(..)
, Meta(..)
, __
, MName
, prettyMName
, QName(..)
, RName(..)
, (.:.)
, toQ
, LName(..)
, Name(..)
, Assoc(..)
, Op(..)
, formatOp
, OpN(..)
, formatOpN
, AName(..)
, (//)
, anm
) where

import           Data.Foldable (foldl', foldr', toList)
import           Data.Functor.Classes (showsUnaryWith)
import           Data.List (intersperse)
import qualified Data.List.NonEmpty as NE
import           Data.String (IsString(..))
import           Data.Text (Text)
import qualified Data.Text as T
import           Facet.Pretty (subscript)
import           Facet.Snoc
import           Facet.Snoc.NonEmpty
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
  toIndexed :: Used -> lv -> ix
  toLeveled :: Used -> ix -> lv

instance DeBruijn Level Index where
  toIndexed (Used (Level d)) (Level level) = Index $ d - level - 1
  toLeveled (Used (Level d)) (Index index) = Level $ d - index - 1

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
__ = U T.empty


type MName = NonEmpty Name

prettyMName :: Printer a => MName -> a
prettyMName (ns:|>n) = foldr' (surround dot . pretty) (pretty n) ns

showsModuleName :: (Foldable t, Show a, Show b) => String -> t a -> b -> Int -> ShowS
showsModuleName c m n p = showParen (p > 9) $ foldl' (.) id (intersperse (showChar '.') (shows <$> toList m)) . showString c . showsPrec 10 n



-- | Qualified names, consisting of a module name and declaration name.
data QName = Snoc Name :. Name
  deriving (Eq, Ord)

instance Show QName where
  showsPrec p (m :. n) = showsModuleName ":." m n p

instance P.Pretty QName where
  pretty (m :. n) = foldr' (surround dot . pretty) (pretty n) m


-- | Resolved names.
data RName = MName :.: Name
  deriving (Eq, Ord)

instance Show RName where
  showsPrec p (m :.: n) = showsModuleName ":.:" m n p

instance P.Pretty RName where
  pretty (m :.: n) = foldr' (surround dot . pretty) (pretty n) m

-- | Append a 'Name' onto an 'RName'.
(.:.) :: RName -> Name -> RName
m :.: n .:. n' = (m |> n) :.: n'

-- | Weaken an 'RName' to a 'QName'. This is primarily used for performing lookups in the graph starting from an 'RName' where the stronger structure is not required.
toQ :: RName -> QName
toQ (m :.: n) = toSnoc m :. n


-- | Local names, consisting of a 'Level' or 'Index' to a pattern in an 'Env' or 'Context' and a 'Name' bound by said pattern.
data LName v = LName
  { ident :: v
  , name  :: Name
  }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance DeBruijn lv ix => DeBruijn (LName lv) (LName ix) where
  toIndexed = fmap . toIndexed
  toLeveled = fmap . toLeveled


-- | Declaration names; a choice of textual or operator names.
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


-- | Agency-generated names à la /I Am Not a Number, I Am a Free Variable/.
data AName
  = Root
  | AName :// (Name, Int)
  deriving (Eq, Ord, Show)

infixl 6 ://

instance Semigroup AName where
  xs <> Root       = xs
  xs <> (ys :// y) = (xs <> ys) :// y

instance P.Pretty AName where
  pretty = \case
    Root              -> P.pretty '_'
    Root   :// (n, i) -> P.pretty n <> if i <= 0 then mempty else subscript i
    parent :// (n, i) -> P.pretty parent <> "." <> P.pretty n <> if i <= 0 then mempty else subscript i

(//) :: AName -> Name -> AName
parent // name = parent :// (name, 0)

infixl 6 //

anm :: Name -> AName
anm = (Root //)
