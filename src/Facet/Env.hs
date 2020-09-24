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
) where

import qualified Control.Category as C

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
