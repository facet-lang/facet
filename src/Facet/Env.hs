{-# LANGUAGE RankNTypes #-}
module Facet.Env
( Extends(..)
, refl
, trans
) where

newtype Extends c d = Extends { cast :: forall t . c t -> d t }

refl :: Extends c c
refl = Extends id

trans :: Extends c d -> Extends d e -> Extends c e
trans f g = Extends (cast g . cast f)
