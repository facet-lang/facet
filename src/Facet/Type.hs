{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
module Facet.Type
( Type(..)
) where

import           Control.Monad (ap, guard)
import qualified Facet.Core as C
import qualified Facet.Print as P
import           Silkscreen (pretty)

-- FIXME: distinguish Type-with-Var from Type-without-Var?
data Type a
  = Var a
  | Type
  | Unit
  | Type a :* Type a
  | Type a :$ Type a
  | Type a :-> Type a
  | ForAll (Type a) (Type (Maybe a))
  deriving (Foldable, Functor, Traversable)

infixl 7 :*
infixr 0 :->
infixl 9 :$

instance Applicative Type where
  pure = Var
  (<*>) = ap

instance Monad Type where
  m >>= k = case m of
    Var a      -> k a
    Type       -> Type
    Unit       -> Unit
    l :* r     -> (l >>= k) :* (r >>= k)
    f :$ a     -> (f >>= k) :$ (a >>= k)
    a :-> b    -> (a >>= k) :-> (b >>= k)
    ForAll t b -> ForAll (t >>= k) (b >>= traverse k)

instance Eq a => Eq (Type a) where
  (==) = go
    where
    go :: Eq a => Type a -> Type a -> Bool
    go = curry $ \case
      (Var a1, Var a2) -> a1 == a2
      (Type, Type) -> True
      (Unit, Unit) -> True
      (l1 :* r1, l2 :* r2) -> go l1 l2 && go r1 r2
      (f1 :$ a1, f2 :$ a2) -> go f1 f2 && go a1 a2
      (a1 :-> b1, a2 :-> b2) -> go a1 a2 && go b1 b2
      (ForAll t1 b1, ForAll t2 b2) -> go t1 t2 && go b1 b2
      _ -> False

instance Show a => Show (Type a) where
  showsPrec p = showsPrec p . P.prettyWith P.terminalStyle . C.interpret . fmap (pretty . show)

instance C.Type (Type ()) where
  _Type = Type
  _Unit = Unit
  (.*) = (:*)
  (.$) = (:$)
  (-->) = (:->)
  t >=> b = ForAll t (abstract () (b (Var ())))

instance C.Interpret Type where
  interpret = \case
    Var v -> v
    Type -> C._Type
    Unit -> C._Unit
    f :$ a -> C.interpret f C..$ C.interpret a
    l :* r -> C.interpret l C..* C.interpret r
    a :-> b -> C.interpret a C.--> C.interpret b
    ForAll t b -> C.interpret t C.>=> C.interpret . (`instantiate` b) . Var


abstract :: Eq a => a -> Type a -> Type (Maybe a)
abstract a = fmap (\ x -> x <$ guard (x /= a))

instantiate :: Type a -> Type (Maybe a) -> Type a
instantiate t b = b >>= maybe t Var
