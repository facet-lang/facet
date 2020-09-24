{-# LANGUAGE RankNTypes #-}
module Facet.Env
( Extends
) where

type Extends repr c d = forall t . repr c t -> repr d t
