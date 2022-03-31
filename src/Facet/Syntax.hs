{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
module Facet.Syntax
( -- * Term containers
  IsPair(..)
, HasTerm(..)
, tm
, (:::)(..)
, ty
, _ty
, (:=:)(..)
, nm
, def
, (:@)(..)
, qty
  -- * Variables
, Var(..)
  -- * Decomposition
, splitl
, splitr
  -- * Assertion data
, Exp(..)
, Act(..)
  -- * Type-safe constructors
, T(..)
  -- * Natural transformations
, type (~>)
  -- * Annotations
, Ann(..)
, ann_
, context_
, out_
, annUnary
, annBinary
, Comment(..)
) where

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Function (on)
import Data.Functor.Classes
import Data.Kind (Type)
import Data.Text (Text)
import Facet.Name
import Facet.Snoc
import Facet.Span
import Fresnel.Getter (view)
import Fresnel.Iso (Iso, iso)
import Fresnel.Lens (Lens, Lens', lens)

-- Term containers

class IsPair p where
  pair_ :: Iso (p a b) (p a' b') (a, b) (a', b')


class HasTerm p where
  tm_ :: Lens (p s t) (p s' t) s s'

tm :: HasTerm p => a `p` b -> a
tm = view tm_


data a ::: b = a ::: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 2 :::

instance Bifoldable (:::) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (:::) where
  bimap = bimapDefault

instance Bitraversable (:::) where
  bitraverse f g (a ::: b) = (:::) <$> f a <*> g b

instance Eq a => Eq1 ((:::) a) where
  liftEq = liftEq2 (==)

instance Ord a => Ord1 ((:::) a) where
  liftCompare = liftCompare2 compare

instance Eq2 (:::) where
  liftEq2 eqA eqB (a1 ::: b1) (a2 ::: b2) = eqA a1 a2 && eqB b1 b2

instance Ord2 (:::) where
  liftCompare2 compareA compareB (a1 ::: b1) (a2 ::: b2) = compareA a1 a2 <> compareB b1 b2

instance IsPair (:::) where
  pair_ = iso ((,) <$> tm <*> ty) (uncurry (:::))

instance HasTerm (:::) where
  tm_ = lens (\ (a ::: _) -> a) (\ (_ ::: t) s' -> s' ::: t)

ty :: a ::: b -> b
ty (_ ::: b) = b

_ty :: Lens (s ::: t) (s ::: t') t t'
_ty = lens ty (\ (s ::: _) t' -> s ::: t')


data a :=: b = a :=: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 2 :=:

instance Bifoldable (:=:) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (:=:) where
  bimap = bimapDefault

instance Bitraversable (:=:) where
  bitraverse f g (a :=: b) = (:=:) <$> f a <*> g b

instance IsPair (:=:) where
  pair_ = iso ((,) <$> nm <*> def) (uncurry (:=:))

instance HasTerm (:=:) where
  tm_ = lens (\ (a :=: _) -> a) (\ (_ :=: t) s' -> s' :=: t)

nm :: a :=: b -> a
nm (a :=: _) = a

def :: a :=: b -> b
def (_ :=: b) = b


data a :@ b = a :@ b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 1 :@

instance Bifoldable (:@) where
  bifoldMap = bifoldMapDefault

instance Bifunctor (:@) where
  bimap = bimapDefault

instance Bitraversable (:@) where
  bitraverse f g (a :@ b) = (:@) <$> f a <*> g b

instance IsPair (:@) where
  pair_ = iso ((,) <$> tm <*> qty) (uncurry (:@))

instance HasTerm (:@) where
  tm_ = lens (\ (a :@ _) -> a) (\ (_ :@ t) s' -> s' :@ t)

qty :: p :@ q -> q
qty (_ :@ q) = q


-- Variables

data Var a
  = Global RName -- ^ Global variables, considered equal by 'RName'.
  | Free a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance DeBruijn lv ix => DeBruijn (Var lv) (Var ix) where
  toIndexed = fmap . toIndexed
  toLeveled = fmap . toLeveled


-- Decomposition

splitl :: (t -> Maybe (t, a)) -> t -> (t, Snoc a)
splitl un = go id
  where
  go as t = case un t of
    Just (t', a) -> go (as . (:> a)) t'
    Nothing      -> (t, as Nil)

splitr :: (t -> Maybe (a, t)) -> t -> ([a], t)
splitr un = go id
  where
  go as t = case un t of
    Just (a, t') -> go (as . (a:)) t'
    Nothing      -> (as [], t)


-- Assertion data

newtype Exp a = Exp { getExp :: a }
  deriving (Functor)

newtype Act a = Act { getAct :: a }
  deriving (Functor)


-- Type-safe constructors

type T :: Type -> forall k . k -> Type

newtype T a b = T { getT :: a }


-- Natural transformations

type i ~> j = forall x . i x -> j x


-- Annotations

data Ann a = Ann
  { ann     :: Span
  , context :: Snoc (Span, Comment)
  , out     :: a
  }
  deriving (Foldable, Functor, Traversable)

instance Eq a => Eq (Ann a) where
  (==) = (==) `on` out

instance Ord a => Ord (Ann a) where
  compare = compare `on` out

instance Show a => Show (Ann a) where
  showsPrec p = showsPrec p . out

instance HasSpan (Ann a) where
  span_ = ann_

ann_ :: Lens' (Ann a) Span
ann_ = lens ann (\ a ann -> a{ ann })

context_ :: Lens (Ann a) (Ann a) (Snoc (Span, Comment)) (Snoc (Span, Comment))
context_ = lens context (\ a context -> a{ context })

out_ :: Lens (Ann a) (Ann b) a b
out_ = lens out (\ a out -> a{ out })


annUnary :: (Ann a -> a) -> Ann a -> Ann a
annUnary f a = Ann (ann a) Nil (f a)

annBinary :: (Ann a -> Ann b -> a) -> Ann a -> Ann b -> Ann a
annBinary f a b = Ann (ann a <> ann b) Nil (f a b)


newtype Comment = Comment { getComment :: Text }
  deriving (Eq, Show)
