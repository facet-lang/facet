{-# LANGUAGE RankNTypes #-}
module Facet.Env
( Extends(..)
, refl
, trans
, (C.>>>)
, (^>>)
) where

import qualified Control.Category as C

newtype Extends c d = Extends { cast :: forall t . c t -> d t }

instance C.Category Extends where
  id = refl
  (.) = flip trans

refl :: Extends c c
refl = Extends id

trans :: Extends c d -> Extends d e -> Extends c e
trans f g = Extends (cast g . cast f)

(^>>) :: (forall t . a t -> b t) -> Extends b c -> Extends a c
f ^>> g = Extends f C.>>> g

infixr 1 ^>>
