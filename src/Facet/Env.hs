{-# LANGUAGE RankNTypes #-}
module Facet.Env
( Extends
, refl
) where

type Extends c d = forall t . c t -> d t

refl :: Extends c c
refl = id
