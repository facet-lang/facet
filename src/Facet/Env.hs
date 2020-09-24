{-# LANGUAGE RankNTypes #-}
module Facet.Env
( Extends
, refl
, trans
) where

type Extends c d = forall t . c t -> d t

refl :: Extends c c
refl = id

trans :: Extends c d -> Extends d e -> Extends c e
trans = flip (.)
