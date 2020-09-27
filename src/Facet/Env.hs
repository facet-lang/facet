{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Facet.Env
( type (~>)
, Extends(..)
, refl
, trans
, (C.>>>)
, (^>>)
, (>>^)
, Permutable
, castF
, liftBinder
, strengthen
, weaken
) where

import qualified Control.Category as C
import           Data.Distributive (Distributive)
import           Facet.Functor.C ((:.:)(..), liftCInner)
import           Facet.Functor.I (I(..))

type (c ~> d) = forall t . c t -> d t

newtype Extends c d = Extends { cast :: c ~> d }

instance C.Category Extends where
  id = refl
  (.) = flip trans

refl :: Extends c c
refl = Extends id

trans :: Extends c d -> Extends d e -> Extends c e
trans f g = Extends (cast g . cast f)

(^>>) :: (a ~> b) -> Extends b c -> Extends a c
f ^>> g = Extends f C.>>> g

infixr 1 ^>>

(>>^) :: Extends a b -> (b ~> c) -> Extends a c
f >>^ g = f C.>>> Extends g

infixr 1 >>^


type Permutable i = (Applicative i, Distributive i)

castF :: Functor m => Extends a b -> m (a x) -> m (b x)
castF e = fmap (cast e)

liftBinder :: (Applicative m, Applicative env) => (forall env' . Applicative env' => Extends env env' -> env' a -> m (env' b)) -> m (env (a -> b))
liftBinder f = getC <$> f (Extends liftCInner) (C (pure id))


strengthen :: Functor m => m (I a) -> m a
strengthen = fmap getI

weaken :: (Functor m, Applicative env) => m a -> m (env a)
weaken = fmap pure
