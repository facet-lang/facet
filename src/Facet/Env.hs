{-# LANGUAGE RankNTypes #-}
module Facet.Env
( Extends
) where

type Extends c d = forall t . c t -> d t
